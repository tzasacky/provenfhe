#!/usr/bin/env python3
"""UNTRUSTED test: the SHA-256 of openfhe/fhecheck-tracer.h (the tracer's content identity) agrees
with Python's hashlib on the FIPS 180-4 test vectors, a long message and a word as the tracer feeds
it. The class is cut out of the header and compiled alone (needs a C++ compiler, `c++`; skipped with
exit 0 and a note if there is none). Run from harness/frontend."""
import hashlib
import os
import shutil
import struct
import subprocess
import sys
import tempfile

src = open("openfhe/fhecheck-tracer.h").read()
start = src.index("class Sha256 {")
end = src.index("\n};", start) + 3
if not shutil.which("c++"):
    print("sha256_test: SKIPPED (no c++)")
    sys.exit(0)
msgs = [b"", b"abc", b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq", b"a" * 1000, bytes(range(256)) * 3]
prog = ("#include <cstdint>\n#include <cstring>\n#include <string>\n#include <iostream>\n" + src[start:end] + "\n"
        "int main() {\n"
        + "".join(f'  {{ Sha256 h; const unsigned char m[] = {{{",".join(str(b) for b in m) or "0"}}}; '
                  f'h.update(m, {len(m)}); std::cout << h.hex() << "\\n"; }}\n' for m in msgs)
        + '  { Sha256 h; h.word(0x0102030405060708ULL); std::cout << h.hex() << "\\n"; }\n}\n')
with tempfile.TemporaryDirectory() as d:
    open(os.path.join(d, "t.cpp"), "w").write(prog)
    subprocess.run(["c++", "-std=gnu++17", "-O1", os.path.join(d, "t.cpp"), "-o", os.path.join(d, "t")], check=True)
    got = subprocess.run([os.path.join(d, "t")], capture_output=True, text=True, check=True).stdout.split()
want = [hashlib.sha256(m).hexdigest() for m in msgs] + [hashlib.sha256(struct.pack("<Q", 0x0102030405060708)).hexdigest()]
if got != want:
    print(f"sha256_test: MISMATCH\n  got  {got}\n  want {want}")
    sys.exit(1)
print(f"sha256_test: {len(want)} digests agree with hashlib")
