!Z2147565569_i64 = !mod_arith.int<2147565569 : i64>
!Z2147573761_i64 = !mod_arith.int<2147573761 : i64>
!Z65537_i64 = !mod_arith.int<65537 : i64>
#full_crt_packing_encoding = #lwe.full_crt_packing_encoding<scaling_factor = 1>
#full_crt_packing_encoding1 = #lwe.full_crt_packing_encoding<scaling_factor = 8>
#key = #lwe.key<>
#layout = #tensor_ext.layout<"{ [] -> [ct, slot] : ct = 0 and 0 <= slot <= 1023 }">
#modulus_chain_L1_C0 = #lwe.modulus_chain<elements = <2147565569 : i64, 2147573761 : i64>, current = 0>
#modulus_chain_L1_C1 = #lwe.modulus_chain<elements = <2147565569 : i64, 2147573761 : i64>, current = 1>
!rns_L0 = !rns.rns<!Z2147565569_i64>
!rns_L1 = !rns.rns<!Z2147565569_i64, !Z2147573761_i64>
#original_type = #tensor_ext.original_type<originalType = i64, layout = #layout>
#ring_Z65537_i64_1_x4096 = #polynomial.ring<coefficientType = !Z65537_i64, polynomialModulus = <1 + x**4096>>
#ring_rns_L0_1_x4096 = #polynomial.ring<coefficientType = !rns_L0, polynomialModulus = <1 + x**4096>>
#ring_rns_L1_1_x4096 = #polynomial.ring<coefficientType = !rns_L1, polynomialModulus = <1 + x**4096>>
!pkey_L1 = !lwe.lwe_public_key<key = #key, ring = #ring_rns_L1_1_x4096>
!pt = !lwe.lwe_plaintext<plaintext_space = <ring = #ring_Z65537_i64_1_x4096, encoding = #full_crt_packing_encoding>>
!pt1 = !lwe.lwe_plaintext<plaintext_space = <ring = #ring_Z65537_i64_1_x4096, encoding = #full_crt_packing_encoding1>>
!skey_L0 = !lwe.lwe_secret_key<key = #key, ring = #ring_rns_L0_1_x4096>
#ciphertext_space_L0 = #lwe.ciphertext_space<ring = #ring_rns_L0_1_x4096, encryption_type = lsb>
#ciphertext_space_L1 = #lwe.ciphertext_space<ring = #ring_rns_L1_1_x4096, encryption_type = lsb>
!ct_L0 = !lwe.lwe_ciphertext<plaintext_space = <ring = #ring_Z65537_i64_1_x4096, encoding = #full_crt_packing_encoding1>, ciphertext_space = #ciphertext_space_L0, key = #key, modulus_chain = #modulus_chain_L1_C0>
!ct_L1 = !lwe.lwe_ciphertext<plaintext_space = <ring = #ring_Z65537_i64_1_x4096, encoding = #full_crt_packing_encoding>, ciphertext_space = #ciphertext_space_L1, key = #key, modulus_chain = #modulus_chain_L1_C1>
module attributes {backend.lattigo, bgv.schemeParam = #bgv.scheme_param<logN = 12, Q = [2147565569, 2147573761], P = [2147721217], plaintextModulus = 65537, encryptionTechnique = extended>, scheme.actual_slot_count = 4096 : i64, scheme.bgv, scheme.requested_slot_count = 1024 : i64} {
  func.func @cmux__preprocessing(%arg0: i64, %arg1: i64) -> !preprocessing.storage<!pt> attributes {heir.interface = {entry_arg_indices = array<i64: 1, 0>, func_name = "cmux", roles = ["server.preprocessing"]}} {
    %cst = arith.constant dense<true> : tensor<1024xi1>
    %0 = preprocessing.empty : <!pt>
    %pt = lwe.rlwe_encode %cst <encoding = #full_crt_packing_encoding, ring = #ring_Z65537_i64_1_x4096, level = 1, scale = 1> : tensor<1024xi1> -> !pt
    preprocessing.store %pt, %0[] site 0<!pt> : !pt, <!pt>
    %splat = tensor.splat %arg1 : tensor<1024xi64>
    %pt_0 = lwe.rlwe_encode %splat <encoding = #full_crt_packing_encoding, ring = #ring_Z65537_i64_1_x4096, level = 1, scale = 1> : tensor<1024xi64> -> !pt
    preprocessing.store %pt_0, %0[] site 1<!pt> : !pt, <!pt>
    %splat_1 = tensor.splat %arg0 : tensor<1024xi64>
    %pt_2 = lwe.rlwe_encode %splat_1 <encoding = #full_crt_packing_encoding, ring = #ring_Z65537_i64_1_x4096, level = 1, scale = 1> : tensor<1024xi64> -> !pt
    preprocessing.store %pt_2, %0[] site 2<!pt> : !pt, <!pt>
    return %0 : !preprocessing.storage<!pt>
  }
  func.func @cmux__preprocessed(%arg0: i64, %arg1: i64, %arg2: tensor<1x!ct_L1> {noise.bound = "27.00", tensor_ext.original_type = #tensor_ext.original_type<originalType = i1, layout = #layout>}, %arg3: !preprocessing.storage<!pt>) -> tensor<1x!ct_L0> attributes {heir.interface = {func_name = "cmux", roles = ["client.preprocessed", "server.evaluate"]}} {
    %c0 = arith.constant 0 : index
    %pt = preprocessing.load %arg3[] site 0<!pt> : <!pt>, !pt
    %extracted = tensor.extract %arg2[%c0] : tensor<1x!ct_L1>
    %ct = bgv.sub_plain %pt, %extracted {noise.bound = "27.00"} : (!pt, !ct_L1) -> !ct_L1
    %pt_0 = preprocessing.load %arg3[] site 1<!pt> : <!pt>, !pt
    %ct_1 = bgv.mul_plain %extracted, %pt_0 {noise.bound = "54.00"} : (!ct_L1, !pt) -> !ct_L1
    %pt_2 = preprocessing.load %arg3[] site 2<!pt> : <!pt>, !pt
    %ct_3 = bgv.mul_plain %ct, %pt_2 {noise.bound = "54.00"} : (!ct_L1, !pt) -> !ct_L1
    %ct_4 = bgv.add %ct_1, %ct_3 {noise.bound = "55.00"} : (!ct_L1, !ct_L1) -> !ct_L1
    %0 = tensor.empty() : tensor<1x!ct_L0>
    %ct_5 = bgv.modulus_switch %ct_4 <to_ring = #ring_rns_L0_1_x4096> {noise.bound = "27.17"} : !ct_L1 -> !ct_L0
    %inserted = tensor.insert %ct_5 into %0[%c0] : tensor<1x!ct_L0>
    return %inserted : tensor<1x!ct_L0>
  }
  func.func @cmux(%arg0: i64, %arg1: i64, %arg2: tensor<1x!ct_L1> {noise.bound = "27.00", tensor_ext.original_type = #tensor_ext.original_type<originalType = i1, layout = #layout>}) -> (tensor<1x!ct_L0> {tensor_ext.original_type = #original_type}) attributes {heir.interface = {func_name = "cmux", input_types = [i64, i64, i1], result_types = [i64], roles = ["entry"]}} {
    %0 = call @cmux__preprocessing(%arg1, %arg0) : (i64, i64) -> !preprocessing.storage<!pt>
    %1 = call @cmux__preprocessed(%arg0, %arg1, %arg2, %0) : (i64, i64, tensor<1x!ct_L1>, !preprocessing.storage<!pt>) -> tensor<1x!ct_L0>
    return %1 : tensor<1x!ct_L0>
  }
  func.func @cmux__encrypt__arg2(%arg0: i1, %pk: !pkey_L1) -> tensor<1x!ct_L1> attributes {heir.interface = {func_name = "cmux", index = 2 : i64, roles = ["client.encrypt"]}} {
    %splat = tensor.splat %arg0 : tensor<1024xi1>
    %pt = lwe.rlwe_encode %splat <encoding = #full_crt_packing_encoding, ring = #ring_Z65537_i64_1_x4096, level = 1, scale = 1> : tensor<1024xi1> -> !pt
    %ct = lwe.rlwe_encrypt %pt, %pk : (!pt, !pkey_L1) -> !ct_L1
    %from_elements = tensor.from_elements %ct : tensor<1x!ct_L1>
    return %from_elements : tensor<1x!ct_L1>
  }
  func.func @cmux__decrypt__result0(%arg0: tensor<1x!ct_L0>, %sk: !skey_L0) -> i64 attributes {heir.interface = {func_name = "cmux", index = 0 : i64, roles = ["client.decrypt"]}} {
    %c0 = arith.constant 0 : index
    %extracted = tensor.extract %arg0[%c0] : tensor<1x!ct_L0>
    %pt = lwe.rlwe_decrypt %extracted, %sk : (!ct_L0, !skey_L0) -> !pt1
    %0 = lwe.rlwe_decode %pt <encoding = #full_crt_packing_encoding1, ring = #ring_Z65537_i64_1_x4096> : !pt1 -> tensor<1x1024xi64>
    %extracted_0 = tensor.extract %0[%c0, %c0] : tensor<1x1024xi64>
    return %extracted_0 : i64
  }
}

