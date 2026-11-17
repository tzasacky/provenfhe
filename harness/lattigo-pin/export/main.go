// Command lattigopin records exact-integer traces of small Lattigo v6.2.0 BGV programs in the
// lattigo-pin/v1 format (../FORMAT.md). Every ciphertext, plaintext and key is converted to
// coefficient form (INTT if the object is in NTT form, IMForm if it is in Montgomery form) and
// written as canonical residues per limb. Before a case is written the exporter re-derives, from
// exactly the residues it serialises, the t-read phase of every ciphertext and the key equations of
// the relinearisation and Galois keys, and compares Lattigo's own decryption with the cleartext
// evaluation of the program.
package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"math"
	"math/big"
	"math/bits"
	"math/rand/v2"
	"os"
	"path/filepath"
	"sort"
	"strings"

	"github.com/tuneinsight/lattigo/v6/core/rlwe"
	"github.com/tuneinsight/lattigo/v6/ring"
	"github.com/tuneinsight/lattigo/v6/ring/ringqp"
	"github.com/tuneinsight/lattigo/v6/schemes/bgv"
	"github.com/tuneinsight/lattigo/v6/utils/structs"
)

// ---------------------------------------------------------------------------------------------
// JSON shapes (see ../FORMAT.md; fields marked "extra" are additions allowed by the format)

type Poly [][]string

type Op struct {
	Op   string `json:"op"`
	Pt   string `json:"pt,omitempty"`
	A    string `json:"a,omitempty"`
	B    string `json:"b,omitempty"`
	C    string `json:"c,omitempty"`
	G    string `json:"g,omitempty"`
	Out  string `json:"out"`
	Call string `json:"call,omitempty"`
}

type Obj struct {
	Kind       string   `json:"kind"`
	Level      int      `json:"level"`
	Parts      int      `json:"parts,omitempty"`
	Scale      string   `json:"scale"`
	Comps      []Poly   `json:"comps,omitempty"`
	Poly       Poly     `json:"poly,omitempty"`
	TPhaseLog2 *float64 `json:"tPhaseLog2,omitempty"` // extra: log2 max |centred t*phase mod Q_level|
}

type Digit struct {
	B Poly `json:"b"`
	A Poly `json:"a"`
}

type Key struct {
	G         string    `json:"g,omitempty"`
	GInv      string    `json:"gInv,omitempty"`      // extra
	KeySecret string    `json:"keySecret,omitempty"` // extra: secret the key is encrypted under
	Target    string    `json:"target,omitempty"`    // extra: secret the key encrypts
	Digits    []Digit   `json:"digits"`              // GadgetCiphertext.Value[i][0]
	Gadget    [][]Digit `json:"gadget,omitempty"`    // extra (base2 != 0 only): Value[i][j], all j
}

type Keys struct {
	Relin  Key   `json:"relin"`
	Galois []Key `json:"galois"`
}

type Slot struct {
	Expected []string `json:"expected"`
	Decoded  []string `json:"decoded"`
	Match    bool     `json:"match"` // extra
}

type Case struct {
	Format    string           `json:"format"`
	Case      string           `json:"case"`
	Suite     string           `json:"suite"` // extra
	Generator string           `json:"generator"`
	Lattigo   string           `json:"lattigo"`
	Seed      uint64           `json:"seed"`
	LogN      int              `json:"logN"`
	N         int              `json:"N"`
	T         string           `json:"t"`
	Qs        []string         `json:"qs"`
	Ps        []string         `json:"ps"`
	Base2     int              `json:"base2"`
	Secret    []int64          `json:"secret"`
	Keys      Keys             `json:"keys"`
	Objects   map[string]*Obj  `json:"objects"`
	Ops       []Op             `json:"ops"`
	Slots     map[string]*Slot `json:"slots"`
	Notes     []string         `json:"notes"`
}

// ---------------------------------------------------------------------------------------------
// modular helpers

func mulmod(a, b, m uint64) uint64 {
	hi, lo := bits.Mul64(a, b)
	return bits.Rem64(hi, lo, m)
}
func addmod(a, b, m uint64) uint64 {
	s := a + b
	if s >= m || s < a {
		s -= m
	}
	return s
}
func submod(a, b, m uint64) uint64 {
	if a >= b {
		return a - b
	}
	return a + (m - b)
}
func smallMod(v int64, m uint64) uint64 {
	if v >= 0 {
		return uint64(v) % m
	}
	return submod(0, uint64(-v)%m, m)
}
func centre(v, m uint64) int64 {
	if v > m/2 {
		return -int64(m - v)
	}
	return int64(v)
}

// negacyclic product of a residue poly mod m with a small signed integer poly.
func mulSmall(a []uint64, s []int64, m uint64) []uint64 {
	N := len(a)
	res := make([]uint64, N)
	for i := 0; i < N; i++ {
		if a[i] == 0 {
			continue
		}
		for j := 0; j < N; j++ {
			if s[j] == 0 {
				continue
			}
			sv, neg := s[j], false
			if sv < 0 {
				sv, neg = -sv, true
			}
			p := mulmod(a[i], uint64(sv)%m, m)
			k := i + j
			if k >= N {
				k -= N
				neg = !neg
			}
			if neg {
				res[k] = submod(res[k], p, m)
			} else {
				res[k] = addmod(res[k], p, m)
			}
		}
	}
	return res
}

// negacyclic product of two small integer polys (exact).
func mulInt(a, b []int64) []int64 {
	N := len(a)
	res := make([]int64, N)
	for i := range a {
		for j := range b {
			k, p := i+j, a[i]*b[j]
			if k >= N {
				res[k-N] -= p
			} else {
				res[k] += p
			}
		}
	}
	return res
}

// automorphism X -> X^g on a small integer poly (coefficient domain, negacyclic).
func autom(s []int64, g uint64) []int64 {
	N := uint64(len(s))
	out := make([]int64, N)
	for i := uint64(0); i < N; i++ {
		idx := (i * g) % (2 * N)
		if idx >= N {
			out[idx-N] -= s[i]
		} else {
			out[idx] += s[i]
		}
	}
	return out
}

// CRT-reconstructs the coefficients of a residue poly, centred mod prod(mods); returns max |.| as log2.
func crtMaxLog2(limbs [][]uint64, mods []uint64) (float64, *big.Int) {
	Q := big.NewInt(1)
	for _, m := range mods {
		Q.Mul(Q, new(big.Int).SetUint64(m))
	}
	half := new(big.Int).Rsh(Q, 1)
	N := len(limbs[0])
	maxAbs := new(big.Int)
	for k := 0; k < N; k++ {
		x := new(big.Int)
		for l, m := range mods {
			bm := new(big.Int).SetUint64(m)
			Mi := new(big.Int).Div(Q, bm)
			inv := new(big.Int).ModInverse(new(big.Int).Mod(Mi, bm), bm)
			term := new(big.Int).SetUint64(limbs[l][k])
			term.Mul(term, inv).Mod(term, bm).Mul(term, Mi)
			x.Add(x, term)
		}
		x.Mod(x, Q)
		if x.Cmp(half) > 0 {
			x.Sub(x, Q)
		}
		x.Abs(x)
		if x.Cmp(maxAbs) > 0 {
			maxAbs = x
		}
	}
	if maxAbs.Sign() == 0 {
		return math.Inf(-1), Q
	}
	f, _ := new(big.Float).SetInt(maxAbs).Float64()
	return math.Log2(f), Q
}

func log2Big(x *big.Int) float64 {
	f, _ := new(big.Float).SetInt(x).Float64()
	return math.Log2(f)
}

func strPoly(limbs [][]uint64) Poly {
	p := make(Poly, len(limbs))
	for i, l := range limbs {
		p[i] = make([]string, len(l))
		for j, v := range l {
			p[i][j] = fmt.Sprint(v)
		}
	}
	return p
}

func strVec(v []uint64) []string {
	s := make([]string, len(v))
	for i, x := range v {
		s[i] = fmt.Sprint(x)
	}
	return s
}

func u64s(v []uint64) []string { return strVec(v) }

// ---------------------------------------------------------------------------------------------
// recorder

type Rec struct {
	c      *Case
	params bgv.Parameters
	t      uint64
	N      int
	slots  int
	qs, ps []uint64
	base2  int
	sk     *rlwe.SecretKey
	s, s2  []int64
	ecd    *bgv.Encoder
	encPk  *rlwe.Encryptor
	encSk  *rlwe.Encryptor
	dec    *rlwe.Decryptor
	eval   *bgv.Evaluator
	rng    *rand.Rand
	galCol uint64
	galRow uint64

	strict    bool
	trial     bool
	trialFail string
	order     []string
	cts       map[string]*rlwe.Ciphertext
	exp       map[string][]uint64
	tscale    map[string]uint64
	next      map[string]int
	maxPhase  float64
	maxPhaseC string
	mismatch  []string
	noteSet   []string
}

func (r *Rec) note(f string, a ...any) { r.c.Notes = append(r.c.Notes, fmt.Sprintf(f, a...)) }

// noFilter (flag -nofilter): no self-check failure discards a step or aborts a case; failures
// are only noted. Used to record the honest programs without the phase-size filter, so that a
// key switch far above budget could not be dropped silently.
var noFilter bool

func (r *Rec) fail(f string, a ...any) {
	msg := fmt.Sprintf(f, a...)
	switch {
	case noFilter:
		r.note("self-check (not filtered, -nofilter): %s", msg)
	case r.trial:
		if r.trialFail == "" {
			r.trialFail = msg
		}
	case r.strict:
		panic(fmt.Sprintf("SELF-CHECK FAILED in case %s: %s", r.c.Case, msg))
	default:
		r.note("self-check (non-fatal in this suite): %s", msg)
	}
}

func (r *Rec) newID(prefix string) string {
	r.next[prefix]++
	return fmt.Sprintf("%s%d", prefix, r.next[prefix]-1)
}

// coefficient-form residues of a Q poly (copy, INTT if isNTT, IMForm if isMont).
func (r *Rec) coeffQ(p ring.Poly, isNTT, isMont bool) [][]uint64 {
	rq := r.params.RingQ().AtLevel(p.Level())
	c := *p.CopyNew()
	if isNTT {
		rq.INTT(c, c)
	}
	if isMont {
		rq.IMForm(c, c)
	}
	out := make([][]uint64, p.Level()+1)
	for i := range out {
		out[i] = append([]uint64(nil), c.Coeffs[i][:r.N]...)
	}
	return out
}

// coefficient-form residues of a QP poly: Q limbs then P limbs. Gadget ciphertexts and secret keys carry
// no metadata flags; Lattigo documents and constructs them in NTT and Montgomery form
// (core/rlwe/gadgetciphertext.go NewGadgetCiphertext, keygenerator.go genEvaluationKey/genSecretKeyFromSampler).
func (r *Rec) coeffQP(p ringqp.Poly) [][]uint64 {
	out := r.coeffQ(p.Q, true, true)
	if len(r.ps) > 0 && p.LevelP() >= 0 {
		rp := r.params.RingP().AtLevel(p.LevelP())
		c := *p.P.CopyNew()
		rp.INTT(c, c)
		rp.IMForm(c, c)
		for i := 0; i <= p.LevelP(); i++ {
			out = append(out, append([]uint64(nil), c.Coeffs[i][:r.N]...))
		}
	}
	return out
}

func (r *Rec) decode(ct *rlwe.Ciphertext) []uint64 {
	v := make([]uint64, r.slots)
	if err := r.ecd.Decode(r.dec.DecryptNew(ct), v); err != nil {
		panic(err)
	}
	return v
}

// tPhase: per limb (c0 + c1 s + c2 s^2) * t mod q_l, from the serialised residues.
func (r *Rec) tPhase(comps [][][]uint64) float64 {
	level := len(comps[0])
	spow := [][]int64{nil, r.s, r.s2}
	limbs := make([][]uint64, level)
	for l := 0; l < level; l++ {
		m := r.qs[l]
		acc := append([]uint64(nil), comps[0][l]...)
		for k := 1; k < len(comps); k++ {
			prod := mulSmall(comps[k][l], spow[k], m)
			for i := range acc {
				acc[i] = addmod(acc[i], prod[i], m)
			}
		}
		tm := r.t % m
		for i := range acc {
			acc[i] = mulmod(acc[i], tm, m)
		}
		limbs[l] = acc
	}
	lg, _ := crtMaxLog2(limbs, r.qs[:level])
	return lg
}

type mark struct {
	nOps, nOrder int
	next         map[string]int
	maxPhase     float64
	maxPhaseC    string
}

func (r *Rec) mark() mark {
	nx := map[string]int{}
	for k, v := range r.next {
		nx[k] = v
	}
	return mark{len(r.c.Ops), len(r.order), nx, r.maxPhase, r.maxPhaseC}
}

func (r *Rec) rollback(m mark) {
	for _, id := range r.order[m.nOrder:] {
		delete(r.c.Objects, id)
		delete(r.c.Slots, id)
		delete(r.cts, id)
		delete(r.exp, id)
		delete(r.tscale, id)
	}
	r.order = r.order[:m.nOrder]
	r.c.Ops = r.c.Ops[:m.nOps]
	r.next = m.next
	r.maxPhase, r.maxPhaseC = m.maxPhase, m.maxPhaseC
}

func (r *Rec) regPt(pt *rlwe.Plaintext) string {
	id := r.newID("pt")
	limbs := r.coeffQ(pt.Value, pt.IsNTT, pt.IsMontgomery)
	if len(limbs) != pt.Level()+1 {
		panic("pt limb count")
	}
	r.c.Objects[id] = &Obj{Kind: "pt", Level: pt.Level() + 1, Scale: fmt.Sprint(pt.Scale.Uint64()), Poly: strPoly(limbs)}
	r.order = append(r.order, id)
	return id
}

// regCt serialises ct, runs the self-checks on the serialised residues and records slots.
func (r *Rec) regCt(ct *rlwe.Ciphertext, exp []uint64, tscale uint64, expectWrong bool) string {
	id := r.newID("ct")
	level := ct.Level() + 1
	comps := make([][][]uint64, ct.Degree()+1)
	pc := make([]Poly, len(comps))
	for k := range comps {
		comps[k] = r.coeffQ(ct.Value[k], ct.IsNTT, ct.IsMontgomery)
		if len(comps[k]) != level {
			panic(fmt.Sprintf("ct %s comp %d has %d limbs, level %d", id, k, len(comps[k]), level))
		}
		pc[k] = strPoly(comps[k])
	}
	lg := r.tPhase(comps)
	logQ := 0.0
	for _, q := range r.qs[:level] {
		logQ += math.Log2(float64(q))
	}
	if lg >= logQ-2 {
		r.fail("%s: log2|t*phase| = %.2f >= log2(Q_level/4) = %.2f", id, lg, logQ-2)
	}
	if lg > r.maxPhase {
		r.maxPhase, r.maxPhaseC = lg, fmt.Sprintf("%s (level %d, log2 Q_level %.1f)", id, level, logQ)
	}
	lgc := math.Round(lg*100) / 100
	r.c.Objects[id] = &Obj{Kind: "ct", Level: level, Parts: ct.Degree() + 1, Scale: fmt.Sprint(ct.Scale.Uint64()), Comps: pc, TPhaseLog2: &lgc}
	r.order = append(r.order, id)
	if ct.Scale.Uint64() != tscale {
		if expectWrong {
			r.note("%s: Lattigo Scale %d but the correct scale is %d", id, ct.Scale.Uint64(), tscale)
		} else {
			r.fail("%s: Lattigo Scale %d != tracked scale %d", id, ct.Scale.Uint64(), tscale)
		}
	}
	got := r.decode(ct)
	match := true
	for i := range got {
		if got[i] != exp[i] {
			match = false
			break
		}
	}
	r.c.Slots[id] = &Slot{Expected: strVec(exp), Decoded: strVec(got), Match: match}
	if !match {
		if expectWrong {
			r.note("%s: decoded != expected (expected for this demonstration)", id)
		} else {
			r.fail("%s: decoded != expected", id)
		}
		if !r.trial {
			r.mismatch = append(r.mismatch, id)
		}
	} else if expectWrong {
		r.note("%s: decoded == expected although the defect predicts a wrong result", id)
	}
	r.cts[id], r.exp[id], r.tscale[id] = ct, exp, tscale
	return id
}

func (r *Rec) randVec() []uint64 {
	v := make([]uint64, r.slots)
	for i := range v {
		v[i] = r.rng.Uint64N(r.t)
	}
	return v
}

func (r *Rec) encrypt(level int, pk bool) string {
	x := r.randVec()
	pt := bgv.NewPlaintext(r.params, level)
	if err := r.ecd.Encode(x, pt); err != nil {
		panic(err)
	}
	ptID := r.regPt(pt)
	ct := bgv.NewCiphertext(r.params, 1, level)
	enc, op := r.encSk, "encSk"
	if pk {
		enc, op = r.encPk, "encPk"
	}
	if err := enc.Encrypt(pt, ct); err != nil {
		panic(err)
	}
	id := r.regCt(ct, x, pt.Scale.Uint64(), false)
	r.c.Ops = append(r.c.Ops, Op{Op: op, Pt: ptID, Out: id})
	return id
}

func (r *Rec) mustFresh(out *rlwe.Ciphertext, ins ...string) {
	for _, in := range ins {
		if r.cts[in] == out {
			panic("output aliases an input")
		}
	}
}

func (r *Rec) addSub(sub bool, a, b string) string {
	ca, cb := r.cts[a], r.cts[b]
	if ca.Level() != cb.Level() || !ca.Scale.Equal(cb.Scale) {
		panic(fmt.Sprintf("add/sub of %s,%s with unequal level or scale", a, b))
	}
	out := bgv.NewCiphertext(r.params, max(ca.Degree(), cb.Degree()), ca.Level())
	r.mustFresh(out, a, b)
	exp := make([]uint64, r.slots)
	op := "add"
	var err error
	if sub {
		op = "sub"
		err = r.eval.Sub(ca, cb, out)
		for i := range exp {
			exp[i] = (r.exp[a][i] + r.t - r.exp[b][i]) % r.t
		}
	} else {
		err = r.eval.Add(ca, cb, out)
		for i := range exp {
			exp[i] = (r.exp[a][i] + r.exp[b][i]) % r.t
		}
	}
	if err != nil {
		panic(err)
	}
	id := r.regCt(out, exp, r.tscale[a], false)
	r.c.Ops = append(r.c.Ops, Op{Op: op, A: a, B: b, Out: id})
	return id
}

func (r *Rec) mul(a, b string) string {
	ca, cb := r.cts[a], r.cts[b]
	if ca.Level() != cb.Level() || ca.Degree() != 1 || cb.Degree() != 1 {
		panic("mul operands must be degree 1 at equal level")
	}
	out := bgv.NewCiphertext(r.params, 2, ca.Level())
	r.mustFresh(out, a, b)
	if err := r.eval.Mul(ca, cb, out); err != nil {
		panic(err)
	}
	exp := make([]uint64, r.slots)
	for i := range exp {
		exp[i] = mulmod(r.exp[a][i], r.exp[b][i], r.t)
	}
	id := r.regCt(out, exp, mulmod(r.tscale[a], r.tscale[b], r.t), false)
	r.c.Ops = append(r.c.Ops, Op{Op: "mul", A: a, B: b, Out: id})
	return id
}

func (r *Rec) relin(a string) string {
	ca := r.cts[a]
	if ca.Degree() != 2 {
		panic("relin input must have degree 2")
	}
	out := bgv.NewCiphertext(r.params, 1, ca.Level())
	r.mustFresh(out, a)
	if err := r.eval.Relinearize(ca, out); err != nil {
		panic(err)
	}
	id := r.regCt(out, r.exp[a], r.tscale[a], false)
	r.c.Ops = append(r.c.Ops, Op{Op: "relin", A: a, Out: id})
	return id
}

// slot permutations (verified against Lattigo's decryption in the honest suite):
// RotateColumns(k=1): slot i of row ρ takes slot (i+1 mod n/2) of row ρ; RotateRows swaps the two rows.
func (r *Rec) rotate(a string, rows bool) string {
	ca := r.cts[a]
	if ca.Degree() != 1 {
		panic("rotate input must have degree 1")
	}
	out := bgv.NewCiphertext(r.params, 1, ca.Level())
	r.mustFresh(out, a)
	h := r.slots / 2
	exp := make([]uint64, r.slots)
	var g uint64
	var call string
	var err error
	if rows {
		g, call = r.galRow, "RotateRows"
		err = r.eval.RotateRows(ca, out)
		for i := range exp {
			exp[i] = r.exp[a][(i+h)%r.slots]
		}
	} else {
		g, call = r.galCol, "RotateColumns k=1"
		err = r.eval.RotateColumns(ca, 1, out)
		for i := range exp {
			exp[i] = r.exp[a][(i%h+1)%h+(i/h)*h]
		}
	}
	if err != nil {
		panic(err)
	}
	id := r.regCt(out, exp, r.tscale[a], false)
	r.c.Ops = append(r.c.Ops, Op{Op: "rotate", A: a, G: fmt.Sprint(g), Out: id, Call: call})
	return id
}

func (r *Rec) rescale(a string) string {
	ca := r.cts[a]
	out := bgv.NewCiphertext(r.params, ca.Degree(), ca.Level()-1)
	r.mustFresh(out, a)
	if err := r.eval.Rescale(ca, out); err != nil {
		panic(err)
	}
	q := r.qs[ca.Level()]
	qinv := new(big.Int).ModInverse(new(big.Int).SetUint64(q%r.t), new(big.Int).SetUint64(r.t)).Uint64()
	id := r.regCt(out, r.exp[a], mulmod(r.tscale[a], qinv, r.t), false)
	r.c.Ops = append(r.c.Ops, Op{Op: "rescale", A: a, Out: id})
	return id
}

// mulConst: newOut=false is the in-place call on a copy (correct); newOut=true is MulNew (defect A).
func (r *Rec) mulConst(a string, k uint64, newOut bool) string {
	ca := r.cts[a]
	var out *rlwe.Ciphertext
	var call string
	if newOut {
		var err error
		if out, err = r.eval.MulNew(ca, k); err != nil {
			panic(err)
		}
		call = "MulNew(ct, uint64)"
	} else {
		out = ca.CopyNew()
		if err := r.eval.Mul(out, k, out); err != nil {
			panic(err)
		}
		call = "Mul(ct, uint64, ct) in place on ct.CopyNew()"
	}
	r.mustFresh(out, a)
	exp := make([]uint64, r.slots)
	for i := range exp {
		exp[i] = mulmod(r.exp[a][i], k%r.t, r.t)
	}
	id := r.regCt(out, exp, r.tscale[a], newOut)
	r.c.Ops = append(r.c.Ops, Op{Op: "mulConst", A: a, C: fmt.Sprint(k), Out: id, Call: call})
	return id
}

// ---------------------------------------------------------------------------------------------
// keys

// keyCheck verifies, per limb of QP, b + a*sKey - P*2^(w*j)*target*[limb in digit i] = e, with the same small
// centred e in every limb. Returns max |e| or an error string.
func (r *Rec) keyCheck(mat structs.Matrix[rlwe.VectorQP], sKey, target []int64) (int64, string) {
	levelP := len(r.ps) - 1
	group := 1
	if levelP >= 0 {
		group = levelP + 1
	}
	mods := append(append([]uint64(nil), r.qs...), r.ps...)
	var maxE int64
	for i := range mat {
		for j := range mat[i] {
			b := r.coeffQP(mat[i][j][0])
			a := r.coeffQP(mat[i][j][1])
			if len(b) != len(mods) || len(a) != len(mods) {
				return -1, fmt.Sprintf("digit (%d,%d) has %d limbs, expected %d", i, j, len(b), len(mods))
			}
			var e0 []int64
			for l, m := range mods {
				v := mulSmall(a[l], sKey, m)
				for k := range v {
					v[k] = addmod(v[k], b[l][k], m)
				}
				if l < len(r.qs) && l/group == i {
					f := uint64(1)
					for _, p := range r.ps {
						f = mulmod(f, p%m, m)
					}
					for jj := 0; jj < j*r.base2; jj++ {
						f = mulmod(f, 2, m)
					}
					for k := range v {
						v[k] = submod(v[k], mulmod(f, smallMod(target[k], m), m), m)
					}
				}
				e := make([]int64, r.N)
				for k := range v {
					e[k] = centre(v[k], m)
					if e[k] > maxE {
						maxE = e[k]
					} else if -e[k] > maxE {
						maxE = -e[k]
					}
				}
				if l == 0 {
					e0 = e
				} else {
					for k := range e {
						if e[k] != e0[k] {
							return -1, fmt.Sprintf("digit (%d,%d): e differs between limb 0 and limb %d (coeff %d: %d vs %d)", i, j, l, k, e0[k], e[k])
						}
					}
				}
			}
		}
	}
	return maxE, ""
}

func (r *Rec) exportKey(g *rlwe.GadgetCiphertext) Key {
	var k Key
	for i := range g.Value {
		k.Digits = append(k.Digits, Digit{B: strPoly(r.coeffQP(g.Value[i][0][0])), A: strPoly(r.coeffQP(g.Value[i][0][1]))})
	}
	if r.base2 != 0 {
		for i := range g.Value {
			var row []Digit
			for j := range g.Value[i] {
				row = append(row, Digit{B: strPoly(r.coeffQP(g.Value[i][j][0])), A: strPoly(r.coeffQP(g.Value[i][j][1]))})
			}
			k.Gadget = append(k.Gadget, row)
		}
	}
	return k
}

// ---------------------------------------------------------------------------------------------
// case setup

type ParamSet struct {
	Name string
	Lit  bgv.ParametersLiteral
}

func newRec(suite, name string, ps ParamSet, base2 int, seed uint64, strict bool) *Rec {
	params, err := bgv.NewParametersFromLiteral(ps.Lit)
	if err != nil {
		panic(fmt.Sprintf("%s: %v", ps.Name, err))
	}
	r := &Rec{params: params, t: params.PlaintextModulus(), N: params.N(), slots: params.MaxSlots(),
		qs: params.Q(), ps: params.P(), base2: base2, strict: strict,
		rng: rand.New(rand.NewPCG(seed, 0x6c617474696770)),
		cts: map[string]*rlwe.Ciphertext{}, exp: map[string][]uint64{}, tscale: map[string]uint64{},
		next: map[string]int{}, maxPhase: math.Inf(-1)}
	r.c = &Case{Format: "lattigo-pin/v1", Case: name, Suite: suite, Generator: "harness/lattigo-pin/export (lattigopin)",
		Lattigo: "v6.2.0", Seed: seed, LogN: params.LogN(), N: params.N(), T: fmt.Sprint(r.t),
		Qs: u64s(r.qs), Ps: u64s(r.ps), Base2: base2,
		Objects: map[string]*Obj{}, Slots: map[string]*Slot{}, Ops: []Op{}, Notes: []string{}}
	if r.c.Ps == nil {
		r.c.Ps = []string{}
	}
	r.note("parameter set %s; MaxSlots %d; LogQi %v; LogPi %v", ps.Name, r.slots, params.LogQi(), params.LogPi())

	kgen := rlwe.NewKeyGenerator(params)
	r.sk = kgen.GenSecretKeyNew()
	pk := kgen.GenPublicKeyNew(r.sk)
	var evkp []rlwe.EvaluationKeyParameters
	if base2 != 0 {
		b2 := base2
		evkp = append(evkp, rlwe.EvaluationKeyParameters{BaseTwoDecomposition: &b2})
	}
	r.galCol = params.GaloisElement(1)
	r.galRow = params.GaloisElementOrderTwoOrthogonalSubgroup()
	if r.galRow != params.GaloisElementForRowRotation() {
		panic("row Galois element mismatch")
	}
	rlk := kgen.GenRelinearizationKeyNew(r.sk, evkp...)
	gks := []*rlwe.GaloisKey{kgen.GenGaloisKeyNew(r.galCol, r.sk, evkp...), kgen.GenGaloisKeyNew(r.galRow, r.sk, evkp...)}
	r.eval = bgv.NewEvaluator(params, rlwe.NewMemEvaluationKeySet(rlk, gks...))
	r.ecd = bgv.NewEncoder(params)
	r.encPk = rlwe.NewEncryptor(params, pk)
	r.encSk = rlwe.NewEncryptor(params, r.sk)
	r.dec = rlwe.NewDecryptor(params, r.sk)

	// secret: limb 0 centred; every other Q and P limb must agree.
	sl := r.coeffQP(r.sk.Value)
	mods := append(append([]uint64(nil), r.qs...), r.ps...)
	r.s = make([]int64, r.N)
	for k := range r.s {
		r.s[k] = centre(sl[0][k], mods[0])
	}
	for l, m := range mods {
		for k := range r.s {
			if centre(sl[l][k], m) != r.s[k] {
				panic("secret key limbs disagree")
			}
		}
	}
	r.s2 = mulInt(r.s, r.s)
	r.c.Secret = r.s

	// keys + key self-checks (informational)
	r.c.Keys.Relin = r.exportKey(&rlk.GadgetCiphertext)
	r.c.Keys.Relin.KeySecret, r.c.Keys.Relin.Target = "s", "s^2"
	if e, msg := r.keyCheck(rlk.Value, r.s, r.s2); msg == "" {
		r.note("key check relin: b + a*s = e + P*2^(w*j)*s^2 on digit limbs, max|e| = %d (%d digits x %v)", e, len(rlk.Value), rlk.BaseTwoDecompositionVectorSize())
	} else {
		r.note("key check relin FAILED: %s", msg)
	}
	for _, gk := range gks {
		g := gk.GaloisElement
		gInv := params.ModInvGaloisElement(g)
		k := r.exportKey(&gk.GadgetCiphertext)
		k.G, k.GInv = fmt.Sprint(g), fmt.Sprint(gInv)
		k.Target = "s"
		eInv, mInv := r.keyCheck(gk.Value, autom(r.s, gInv), r.s)
		eG, mG := r.keyCheck(gk.Value, autom(r.s, g), r.s)
		switch {
		case mInv == "":
			k.KeySecret = "pi_{gInv}(s) = s(X^gInv)"
			r.note("key check galois g=%d: under pi_{g^-1}(s) (gInv=%d), target s: max|e| = %d", g, gInv, eInv)
		case mG == "":
			k.KeySecret = "pi_g(s) = s(X^g)"
			r.note("key check galois g=%d: under pi_g(s), target s: max|e| = %d (pi_{g^-1} failed: %s)", g, eG, mInv)
		default:
			r.note("key check galois g=%d FAILED for both conventions: %s / %s", g, mInv, mG)
		}
		r.c.Keys.Galois = append(r.c.Keys.Galois, k)
	}
	r.note("rotation semantics: Automorphism(ct, g) = gadget product of c1 with the key for g (switching s -> pi_{g^-1}(s)), add c0, then apply pi_g (X -> X^g) to both parts (core/rlwe/evaluator_automorphism.go)")
	return r
}

func (r *Rec) finish(dir string) {
	r.note("max log2|centred t*phase| over all ciphertexts: %.2f at %s", r.maxPhase, r.maxPhaseC)
	if len(r.mismatch) > 0 {
		r.note("decoded != expected for: %s", strings.Join(r.mismatch, ", "))
	} else {
		r.note("decoded == expected for every ciphertext")
	}
	if err := os.MkdirAll(dir, 0o755); err != nil {
		panic(err)
	}
	b, err := json.Marshal(r.c)
	if err != nil {
		panic(err)
	}
	p := filepath.Join(dir, r.c.Case+".json")
	if err := os.WriteFile(p+".tmp", append(b, '\n'), 0o644); err != nil {
		panic(err)
	}
	if err := os.Rename(p+".tmp", p); err != nil {
		panic(err)
	}
}

func (r *Rec) level(id string) int { return r.cts[id].Level() }

// randK: a constant in [2, min(2^12, (t-1)/2)]. Lattigo's Mul(ct, *big.Int) reduces k mod t and
// uses k-t when k > t/2; keeping k <= (t-1)/2 makes the recorded "c" the exact integer multiplier.
// Its size multiplies the t-read noise.
func (r *Rec) randK() uint64 { return 2 + r.rng.Uint64N(min((r.t-1)/2-1, 4094)) }

// ---------------------------------------------------------------------------------------------
// programs

func (r *Rec) programHonest() {
	L := r.params.MaxLevel()
	c0, c1 := r.encrypt(L, true), r.encrypt(L, true)
	c2, c3 := r.encrypt(L, false), r.encrypt(L, false)
	c4, c5 := r.encrypt(L-1, true), r.encrypt(L-1, false)
	a := r.addSub(false, c0, c2)
	b := r.addSub(true, c1, c3)
	m := r.mul(a, b)
	rl := r.relin(m)
	r.rotate(rl, false)
	r.rotate(rl, true)
	r.mulConst(rl, r.randK(), false)
	rs2 := r.rescale(rl)
	rs3 := r.rescale(m)
	r3 := r.relin(rs3)
	r.addSub(false, rs2, r3)
	r.addSub(true, r3, rs2)
	e := r.addSub(false, c4, c5)
	r.addSub(true, c5, c4)
	r.rotate(e, false)

	// chain: multiply by a fresh encryption at the current level (alternately pk / sk), relinearise,
	// rescale, then rotate / add / mulConst at the new level. A step whose ciphertexts would reach
	// |t*phase| >= Q_level/4 (or decode wrongly) is discarded and replaced by a plain rescale of the
	// current ciphertext followed by the same rotate / add / mulConst, so every case reaches level 0.
	// attempt runs f as a trial; outside a trial a failing attempt is rolled back and noted.
	attempt := func(what string, lvl int, f func()) {
		if r.trial {
			f()
			return
		}
		mk := r.mark()
		r.trial, r.trialFail = true, ""
		f()
		r.trial = false
		if r.trialFail != "" {
			r.rollback(mk)
			r.note("%s at Lattigo level %d discarded (%s)", what, lvl, r.trialFail)
		}
	}
	after := func(nx string) {
		attempt("rotate/add/rotate", r.level(nx), func() {
			rc := r.rotate(nx, false)
			ad := r.addSub(false, nx, rc)
			r.rotate(ad, true)
		})
		// the constant multiplies the t-read noise by |k|: tried separately
		attempt("mulConst", r.level(nx), func() { r.mulConst(nx, r.randK(), false) })
	}
	cur, partner, steps, plain := rs2, e, 1, 0
	for r.level(cur) > 0 {
		mk := r.mark()
		r.trial, r.trialFail = true, ""
		if steps > 1 {
			partner = r.encrypt(r.level(cur), steps%2 == 0)
		}
		mm := r.mul(cur, partner)
		rr := r.relin(mm)
		nx := r.rescale(rr)
		after(nx)
		r.trial = false
		if r.trialFail != "" {
			r.rollback(mk)
			r.note("mul step at Lattigo level %d discarded (%s); plain rescale instead", r.level(cur), r.trialFail)
			nx = r.rescale(cur)
			after(nx)
			plain++
		} else {
			steps++
		}
		cur = nx
	}
	r.note("multiplicative depth reached: %d, plain rescales in chain: %d (final Lattigo level %d of max %d)", steps, plain, r.level(cur), L)
}

func (r *Rec) programDefect() {
	L := r.params.MaxLevel()
	c0 := r.encrypt(L, true)
	c1 := r.encrypt(L, false)
	m := r.mul(c0, c1)
	rl := r.relin(m)
	r.rotate(c0, false)
	r.rotate(c1, true)
	r.rotate(rl, false)
}

func (r *Rec) programScale() {
	L := r.params.MaxLevel()
	c0 := r.encrypt(L, true)
	c1 := r.encrypt(L, false)
	m := r.mul(c0, c1)
	rl := r.relin(m)
	rs := r.rescale(rl)
	k := r.randK()
	r.mulConst(rs, k, true)
	r.mulConst(rs, k, false)
	r.note("scale demo: input scale %d (Lattigo %d); MulNew(ct, uint64) is probe defect A", r.tscale[rs], r.cts[rs].Scale.Uint64())
}

// ---------------------------------------------------------------------------------------------
// primes for the explicit-modulus suites

func primesNear(start uint64, twoN uint64, down bool, count int, avoid map[uint64]bool) []uint64 {
	var out []uint64
	q := start - (start-1)%twoN // q ≡ 1 mod 2N, q <= start
	if !down && q < start {
		q += twoN
	}
	for len(out) < count {
		if !avoid[q] && new(big.Int).SetUint64(q).ProbablyPrime(30) {
			out = append(out, q)
			avoid[q] = true
		}
		if down {
			q -= twoN
		} else {
			q += twoN
		}
	}
	return out
}

func main() {
	outDir := flag.String("out", "cases", "output directory")
	perSet := flag.Int("per-set", 32, "honest cases per parameter set")
	only := flag.String("suite", "", "only this suite (honest, defectB, defectN, scale)")
	flag.BoolVar(&noFilter, "nofilter", false, "record every step; self-check failures are only noted")
	flag.Parse()

	run := func(s string) bool { return *only == "" || *only == s }
	counts := map[string]int{}

	honestSets := []ParamSet{
		{"H1 LogN4 LogQ[30,25,25,25] LogP[30] t65537", bgv.ParametersLiteral{LogN: 4, LogQ: []int{30, 25, 25, 25}, LogP: []int{30}, PlaintextModulus: 65537}},
		{"H2 LogN4 LogQ[32,22,22,22,22] LogP[25,25] t65537", bgv.ParametersLiteral{LogN: 4, LogQ: []int{32, 22, 22, 22, 22}, LogP: []int{25, 25}, PlaintextModulus: 65537}},
		{"H3 LogN5 LogQ[35,30,30] LogP[30,30,30] t257", bgv.ParametersLiteral{LogN: 5, LogQ: []int{35, 30, 30}, LogP: []int{30, 30, 30}, PlaintextModulus: 257}},
		{"H4 LogN5 LogQ[45,28,28,28] LogP[35] t786433", bgv.ParametersLiteral{LogN: 5, LogQ: []int{45, 28, 28, 28}, LogP: []int{35}, PlaintextModulus: 786433}},
	}

	if run("honest") {
		for si, ps := range honestSets {
			for i := 0; i < *perSet; i++ {
				seed := uint64(1000*(si+1) + i)
				name := fmt.Sprintf("honest-h%d-%03d", si+1, i)
				r := newRec("honest", name, ps, 0, seed, true)
				r.programHonest()
				r.finish(filepath.Join(*outDir, "honest"))
				counts["honest"]++
				if i == 0 {
					fmt.Printf("%s: max log2|t*phase| %.2f at %s; ops %d\n", name, r.maxPhase, r.maxPhaseC, len(r.c.Ops))
					for _, n := range r.c.Notes {
						if strings.HasPrefix(n, "key check") || strings.HasPrefix(n, "multiplicative") || strings.HasPrefix(n, "chain") {
							fmt.Println("   ", n)
						}
					}
				}
			}
		}
	}

	if run("defectB") {
		ps := ParamSet{"B LogN4 LogQ[40,40,40] no P t65537", bgv.ParametersLiteral{LogN: 4, LogQ: []int{40, 40, 40}, PlaintextModulus: 65537}}
		for i := 0; i < 5; i++ {
			r := newRec("defectB", fmt.Sprintf("defectB-%03d", i), ps, 0, uint64(5000+i), false)
			r.note("defect B: no P primes with BaseTwoDecomposition = 0; gadgetProductSinglePAndBitDecompLazy takes every digit from limb 0")
			r.programDefect()
			r.finish(filepath.Join(*outDir, "defectB"))
			counts["defectB"]++
			fmt.Printf("%s: mismatches %v\n", r.c.Case, r.mismatch)
		}
	}

	if run("defectN") {
		twoN := uint64(32)
		avoid := map[uint64]bool{}
		q0 := primesNear(1<<40, twoN, true, 1, avoid)[0]
		pBig := primesNear(1<<40, twoN, true, 1, avoid)[0]
		hi := primesNear(1482910, twoN, true, 2, avoid) // (2^20, sqrt2*2^20): bit 20 set in many residues
		lo := primesNear(1<<20, twoN, true, 2, avoid)                             // (sqrt2*2^19, 2^20): fit in 20 bits
		for _, q := range append(append([]uint64{}, hi...), lo...) {
			if math.Round(math.Log2(float64(q))) != 20 {
				panic("prime choice: round(log2 q) != 20")
			}
		}
		mk := func(name string, qs []uint64, withP bool) ParamSet {
			lit := bgv.ParametersLiteral{LogN: 4, Q: qs, PlaintextModulus: 65537}
			if withP {
				lit.P = []uint64{pBig}
			}
			return ParamSet{name, lit}
		}
		type nc struct {
			name    string
			ps      ParamSet
			control bool
		}
		cases := []nc{
			{"defectN-000", mk("N q1,q2 in (2^20, sqrt2*2^20), one P", []uint64{q0, hi[0], hi[1]}, true), false},
			{"defectN-001", mk("N q1,q2 in (2^20, sqrt2*2^20), one P", []uint64{q0, hi[0], hi[1]}, true), false},
			{"defectN-002", mk("N q1,q2 in (2^20, sqrt2*2^20), one P", []uint64{q0, hi[0], hi[1]}, true), false},
			{"defectN-003", mk("N q1,q2 in (2^20, sqrt2*2^20), no P", []uint64{q0, hi[0], hi[1]}, false), false},
			{"defectN-004", mk("N q1,q2 in (2^20, sqrt2*2^20), no P", []uint64{q0, hi[0], hi[1]}, false), false},
			{"defectN-control-000", mk("N control q1,q2 in (sqrt2*2^19, 2^20), one P", []uint64{q0, lo[0], lo[1]}, true), true},
			{"defectN-control-001", mk("N control q1,q2 in (sqrt2*2^19, 2^20), no P", []uint64{q0, lo[0], lo[1]}, false), true},
		}
		for i, c := range cases {
			r := newRec("defectN", c.name, c.ps, 20, uint64(6000+i), false)
			if c.control {
				r.note("defect N control: round(log2 q_i) = 20 and q_i < 2^20, so ceil(20/20) = 1 base-2 digit per 20-bit limb covers every residue")
			} else {
				r.note("defect N: round(log2 q_i) = 20 but q_i > 2^20, so residues with bit 20 set are never decomposed (BaseTwoDecompositionVectorSize uses LogQi)")
			}
			r.programDefect()
			r.finish(filepath.Join(*outDir, "defectN"))
			counts["defectN"]++
			fmt.Printf("%s: qs %v ps %v mismatches %v\n", r.c.Case, r.qs, r.ps, r.mismatch)
		}
	}

	if run("scale") {
		for i := 0; i < 3; i++ {
			r := newRec("scale", fmt.Sprintf("scale-%03d", i), honestSets[i%len(honestSets)], 0, uint64(7000+i), true)
			r.programScale()
			r.finish(filepath.Join(*outDir, "scale"))
			counts["scale"]++
			fmt.Printf("%s: mismatches %v\n", r.c.Case, r.mismatch)
		}
	}

	keys := make([]string, 0, len(counts))
	for k := range counts {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	for _, k := range keys {
		fmt.Printf("suite %s: %d cases\n", k, counts[k])
	}
}
