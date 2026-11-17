!Z134250497_i64 = !mod_arith.int<134250497 : i64>
!Z17179967489_i64 = !mod_arith.int<17179967489 : i64>
!Z17180262401_i64 = !mod_arith.int<17180262401 : i64>
!Z17180295169_i64 = !mod_arith.int<17180295169 : i64>
!Z65537_i64 = !mod_arith.int<65537 : i64>
#full_crt_packing_encoding = #lwe.full_crt_packing_encoding<scaling_factor = 1>
#full_crt_packing_encoding1 = #lwe.full_crt_packing_encoding<scaling_factor = 27625>
#full_crt_packing_encoding2 = #lwe.full_crt_packing_encoding<scaling_factor = 21845>
#full_crt_packing_encoding3 = #lwe.full_crt_packing_encoding<scaling_factor = 29128>
#full_crt_packing_encoding4 = #lwe.full_crt_packing_encoding<scaling_factor = 36409>
#full_crt_packing_encoding5 = #lwe.full_crt_packing_encoding<scaling_factor = 63919>
#key = #lwe.key<>
#layout = #tensor_ext.layout<"{ [] -> [ct, slot] : ct = 0 and 0 <= slot <= 1023 }">
#modulus_chain_L3_C0 = #lwe.modulus_chain<elements = <134250497 : i64, 17179967489 : i64, 17180262401 : i64, 17180295169 : i64>, current = 0>
#modulus_chain_L3_C1 = #lwe.modulus_chain<elements = <134250497 : i64, 17179967489 : i64, 17180262401 : i64, 17180295169 : i64>, current = 1>
#modulus_chain_L3_C2 = #lwe.modulus_chain<elements = <134250497 : i64, 17179967489 : i64, 17180262401 : i64, 17180295169 : i64>, current = 2>
#modulus_chain_L3_C3 = #lwe.modulus_chain<elements = <134250497 : i64, 17179967489 : i64, 17180262401 : i64, 17180295169 : i64>, current = 3>
!rns_L0 = !rns.rns<!Z134250497_i64>
!rns_L1 = !rns.rns<!Z134250497_i64, !Z17179967489_i64>
!rns_L2 = !rns.rns<!Z134250497_i64, !Z17179967489_i64, !Z17180262401_i64>
!rns_L3 = !rns.rns<!Z134250497_i64, !Z17179967489_i64, !Z17180262401_i64, !Z17180295169_i64>
#original_type = #tensor_ext.original_type<originalType = i16, layout = #layout>
#ring_Z65537_i64_1_x8192 = #polynomial.ring<coefficientType = !Z65537_i64, polynomialModulus = <1 + x**8192>>
#ring_rns_L0_1_x8192 = #polynomial.ring<coefficientType = !rns_L0, polynomialModulus = <1 + x**8192>>
#ring_rns_L1_1_x8192 = #polynomial.ring<coefficientType = !rns_L1, polynomialModulus = <1 + x**8192>>
#ring_rns_L2_1_x8192 = #polynomial.ring<coefficientType = !rns_L2, polynomialModulus = <1 + x**8192>>
#ring_rns_L3_1_x8192 = #polynomial.ring<coefficientType = !rns_L3, polynomialModulus = <1 + x**8192>>
!pkey_L3 = !lwe.lwe_public_key<key = #key, ring = #ring_rns_L3_1_x8192>
!pt = !lwe.lwe_plaintext<plaintext_space = <ring = #ring_Z65537_i64_1_x8192, encoding = #full_crt_packing_encoding>>
!pt1 = !lwe.lwe_plaintext<plaintext_space = <ring = #ring_Z65537_i64_1_x8192, encoding = #full_crt_packing_encoding1>>
!skey_L0 = !lwe.lwe_secret_key<key = #key, ring = #ring_rns_L0_1_x8192>
#ciphertext_space_L0 = #lwe.ciphertext_space<ring = #ring_rns_L0_1_x8192, encryption_type = lsb>
#ciphertext_space_L1 = #lwe.ciphertext_space<ring = #ring_rns_L1_1_x8192, encryption_type = lsb>
#ciphertext_space_L1_D3 = #lwe.ciphertext_space<ring = #ring_rns_L1_1_x8192, encryption_type = lsb, size = 3>
#ciphertext_space_L2 = #lwe.ciphertext_space<ring = #ring_rns_L2_1_x8192, encryption_type = lsb>
#ciphertext_space_L2_D3 = #lwe.ciphertext_space<ring = #ring_rns_L2_1_x8192, encryption_type = lsb, size = 3>
#ciphertext_space_L3 = #lwe.ciphertext_space<ring = #ring_rns_L3_1_x8192, encryption_type = lsb>
#ciphertext_space_L3_D3 = #lwe.ciphertext_space<ring = #ring_rns_L3_1_x8192, encryption_type = lsb, size = 3>
!ct_L0 = !lwe.lwe_ciphertext<plaintext_space = <ring = #ring_Z65537_i64_1_x8192, encoding = #full_crt_packing_encoding1>, ciphertext_space = #ciphertext_space_L0, key = #key, modulus_chain = #modulus_chain_L3_C0>
!ct_L1 = !lwe.lwe_ciphertext<plaintext_space = <ring = #ring_Z65537_i64_1_x8192, encoding = #full_crt_packing_encoding4>, ciphertext_space = #ciphertext_space_L1, key = #key, modulus_chain = #modulus_chain_L3_C1>
!ct_L1_1 = !lwe.lwe_ciphertext<plaintext_space = <ring = #ring_Z65537_i64_1_x8192, encoding = #full_crt_packing_encoding5>, ciphertext_space = #ciphertext_space_L1, key = #key, modulus_chain = #modulus_chain_L3_C1>
!ct_L1_D3 = !lwe.lwe_ciphertext<plaintext_space = <ring = #ring_Z65537_i64_1_x8192, encoding = #full_crt_packing_encoding5>, ciphertext_space = #ciphertext_space_L1_D3, key = #key, modulus_chain = #modulus_chain_L3_C1>
!ct_L2 = !lwe.lwe_ciphertext<plaintext_space = <ring = #ring_Z65537_i64_1_x8192, encoding = #full_crt_packing_encoding2>, ciphertext_space = #ciphertext_space_L2, key = #key, modulus_chain = #modulus_chain_L3_C2>
!ct_L2_1 = !lwe.lwe_ciphertext<plaintext_space = <ring = #ring_Z65537_i64_1_x8192, encoding = #full_crt_packing_encoding3>, ciphertext_space = #ciphertext_space_L2, key = #key, modulus_chain = #modulus_chain_L3_C2>
!ct_L2_D3 = !lwe.lwe_ciphertext<plaintext_space = <ring = #ring_Z65537_i64_1_x8192, encoding = #full_crt_packing_encoding3>, ciphertext_space = #ciphertext_space_L2_D3, key = #key, modulus_chain = #modulus_chain_L3_C2>
!ct_L3 = !lwe.lwe_ciphertext<plaintext_space = <ring = #ring_Z65537_i64_1_x8192, encoding = #full_crt_packing_encoding>, ciphertext_space = #ciphertext_space_L3, key = #key, modulus_chain = #modulus_chain_L3_C3>
!ct_L3_D3 = !lwe.lwe_ciphertext<plaintext_space = <ring = #ring_Z65537_i64_1_x8192, encoding = #full_crt_packing_encoding>, ciphertext_space = #ciphertext_space_L3_D3, key = #key, modulus_chain = #modulus_chain_L3_C3>
module attributes {backend.lattigo, bgv.schemeParam = #bgv.scheme_param<logN = 13, Q = [134250497, 17179967489, 17180262401, 17180295169], P = [17180393473, 17180557313], plaintextModulus = 65537, encryptionTechnique = extended>, scheme.actual_slot_count = 8192 : i64, scheme.bgv, scheme.requested_slot_count = 1024 : i64} {
  func.func @mult_dep(%arg0: tensor<1x!ct_L3> {noise.bound = "23.50", tensor_ext.original_type = #original_type}) -> (tensor<1x!ct_L0> {tensor_ext.original_type = #original_type}) attributes {heir.interface = {func_name = "mult_dep", input_types = [i16], result_types = [i16], roles = ["entry", "server.evaluate"]}} {
    %c0 = arith.constant 0 : index
    %extracted = tensor.extract %arg0[%c0] : tensor<1x!ct_L3>
    %ct = bgv.mul %extracted, %extracted {noise.bound = "54.83"} : (!ct_L3, !ct_L3) -> !ct_L3_D3
    %ct_0 = bgv.relinearize %ct <from_basis = [0, 1, 2], to_basis = [0, 1]> {noise.bound = "54.83"} : !ct_L3_D3 -> !ct_L3
    %ct_1 = bgv.modulus_switch %ct_0 <to_ring = #ring_rns_L2_1_x8192> {noise.bound = "23.71"} : !ct_L3 -> !ct_L2
    %ct_2 = bgv.mul %ct_1, %ct_1 {noise.bound = "55.21"} : (!ct_L2, !ct_L2) -> !ct_L2_D3
    %ct_3 = bgv.relinearize %ct_2 <from_basis = [0, 1, 2], to_basis = [0, 1]> {noise.bound = "55.21"} : !ct_L2_D3 -> !ct_L2_1
    %ct_4 = bgv.modulus_switch %ct_3 <to_ring = #ring_rns_L1_1_x8192> {noise.bound = "23.77"} : !ct_L2_1 -> !ct_L1
    %ct_5 = bgv.mul %ct_4, %ct_4 {noise.bound = "55.32"} : (!ct_L1, !ct_L1) -> !ct_L1_D3
    %ct_6 = bgv.relinearize %ct_5 <from_basis = [0, 1, 2], to_basis = [0, 1]> {noise.bound = "55.32"} : !ct_L1_D3 -> !ct_L1_1
    %0 = tensor.empty() : tensor<1x!ct_L0>
    %ct_7 = bgv.modulus_switch %ct_6 <to_ring = #ring_rns_L0_1_x8192> {noise.bound = "23.79"} : !ct_L1_1 -> !ct_L0
    %inserted = tensor.insert %ct_7 into %0[%c0] : tensor<1x!ct_L0>
    return %inserted : tensor<1x!ct_L0>
  }
  func.func @mult_dep__encrypt__arg0(%arg0: i16, %pk: !pkey_L3) -> tensor<1x!ct_L3> attributes {heir.interface = {func_name = "mult_dep", index = 0 : i64, roles = ["client.encrypt"]}} {
    %splat = tensor.splat %arg0 : tensor<1024xi16>
    %pt = lwe.rlwe_encode %splat <encoding = #full_crt_packing_encoding, ring = #ring_Z65537_i64_1_x8192, level = 3, scale = 1> : tensor<1024xi16> -> !pt
    %ct = lwe.rlwe_encrypt %pt, %pk : (!pt, !pkey_L3) -> !ct_L3
    %from_elements = tensor.from_elements %ct : tensor<1x!ct_L3>
    return %from_elements : tensor<1x!ct_L3>
  }
  func.func @mult_dep__decrypt__result0(%arg0: tensor<1x!ct_L0>, %sk: !skey_L0) -> i16 attributes {heir.interface = {func_name = "mult_dep", index = 0 : i64, roles = ["client.decrypt"]}} {
    %c0 = arith.constant 0 : index
    %extracted = tensor.extract %arg0[%c0] : tensor<1x!ct_L0>
    %pt = lwe.rlwe_decrypt %extracted, %sk : (!ct_L0, !skey_L0) -> !pt1
    %0 = lwe.rlwe_decode %pt <encoding = #full_crt_packing_encoding1, ring = #ring_Z65537_i64_1_x8192> : !pt1 -> tensor<1x1024xi16>
    %extracted_0 = tensor.extract %0[%c0, %c0] : tensor<1x1024xi16>
    return %extracted_0 : i16
  }
}

