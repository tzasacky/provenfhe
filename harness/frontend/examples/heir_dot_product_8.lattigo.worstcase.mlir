!Z2147565569_i64 = !mod_arith.int<2147565569 : i64>
!Z281474977349633_i64 = !mod_arith.int<281474977349633 : i64>
!Z4295049217_i64 = !mod_arith.int<4295049217 : i64>
!Z65537_i64 = !mod_arith.int<65537 : i64>
#full_crt_packing_encoding = #lwe.full_crt_packing_encoding<scaling_factor = 1>
#full_crt_packing_encoding1 = #lwe.full_crt_packing_encoding<scaling_factor = 28567>
#full_crt_packing_encoding2 = #lwe.full_crt_packing_encoding<scaling_factor = 23526>
#key = #lwe.key<>
#layout = #tensor_ext.layout<"{ [] -> [ct, slot] : ct = 0 and slot = 0 }">
#modulus_chain_L2_C0 = #lwe.modulus_chain<elements = <4295049217 : i64, 2147565569 : i64, 281474977349633 : i64>, current = 0>
#modulus_chain_L2_C1 = #lwe.modulus_chain<elements = <4295049217 : i64, 2147565569 : i64, 281474977349633 : i64>, current = 1>
#modulus_chain_L2_C2 = #lwe.modulus_chain<elements = <4295049217 : i64, 2147565569 : i64, 281474977349633 : i64>, current = 2>
!rns_L0 = !rns.rns<!Z4295049217_i64>
!rns_L1 = !rns.rns<!Z4295049217_i64, !Z2147565569_i64>
!rns_L2 = !rns.rns<!Z4295049217_i64, !Z2147565569_i64, !Z281474977349633_i64>
#original_type = #tensor_ext.original_type<originalType = i16, layout = #layout>
#ring_Z65537_i64_1_x8192 = #polynomial.ring<coefficientType = !Z65537_i64, polynomialModulus = <1 + x**8192>>
#ring_rns_L0_1_x8192 = #polynomial.ring<coefficientType = !rns_L0, polynomialModulus = <1 + x**8192>>
#ring_rns_L1_1_x8192 = #polynomial.ring<coefficientType = !rns_L1, polynomialModulus = <1 + x**8192>>
#ring_rns_L2_1_x8192 = #polynomial.ring<coefficientType = !rns_L2, polynomialModulus = <1 + x**8192>>
!pkey_L2 = !lwe.lwe_public_key<key = #key, ring = #ring_rns_L2_1_x8192>
!pt = !lwe.lwe_plaintext<plaintext_space = <ring = #ring_Z65537_i64_1_x8192, encoding = #full_crt_packing_encoding>>
!pt1 = !lwe.lwe_plaintext<plaintext_space = <ring = #ring_Z65537_i64_1_x8192, encoding = #full_crt_packing_encoding1>>
!skey_L0 = !lwe.lwe_secret_key<key = #key, ring = #ring_rns_L0_1_x8192>
#ciphertext_space_L0 = #lwe.ciphertext_space<ring = #ring_rns_L0_1_x8192, encryption_type = lsb>
#ciphertext_space_L1 = #lwe.ciphertext_space<ring = #ring_rns_L1_1_x8192, encryption_type = lsb>
#ciphertext_space_L2 = #lwe.ciphertext_space<ring = #ring_rns_L2_1_x8192, encryption_type = lsb>
#ciphertext_space_L2_D3 = #lwe.ciphertext_space<ring = #ring_rns_L2_1_x8192, encryption_type = lsb, size = 3>
!ct_L0 = !lwe.lwe_ciphertext<plaintext_space = <ring = #ring_Z65537_i64_1_x8192, encoding = #full_crt_packing_encoding1>, ciphertext_space = #ciphertext_space_L0, key = #key, modulus_chain = #modulus_chain_L2_C0>
!ct_L1 = !lwe.lwe_ciphertext<plaintext_space = <ring = #ring_Z65537_i64_1_x8192, encoding = #full_crt_packing_encoding2>, ciphertext_space = #ciphertext_space_L1, key = #key, modulus_chain = #modulus_chain_L2_C1>
!ct_L2 = !lwe.lwe_ciphertext<plaintext_space = <ring = #ring_Z65537_i64_1_x8192, encoding = #full_crt_packing_encoding>, ciphertext_space = #ciphertext_space_L2, key = #key, modulus_chain = #modulus_chain_L2_C2>
!ct_L2_D3 = !lwe.lwe_ciphertext<plaintext_space = <ring = #ring_Z65537_i64_1_x8192, encoding = #full_crt_packing_encoding>, ciphertext_space = #ciphertext_space_L2_D3, key = #key, modulus_chain = #modulus_chain_L2_C2>
module attributes {backend.lattigo, bgv.schemeParam = #bgv.scheme_param<logN = 13, Q = [4295049217, 2147565569, 281474977349633], P = [281474977595393, 281474978185217], plaintextModulus = 65537, encryptionTechnique = extended>, scheme.actual_slot_count = 8192 : i64, scheme.bgv, scheme.requested_slot_count = 1024 : i64} {
  func.func @dot_product__preprocessing() -> !preprocessing.storage<!pt> attributes {heir.interface = {entry_arg_indices = array<i64>, func_name = "dot_product", roles = ["server.preprocessing"]}} {
    %cst = arith.constant dense<"0x0100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"> : tensor<1024xi16>
    %0 = preprocessing.empty : <!pt>
    %pt = lwe.rlwe_encode %cst <encoding = #full_crt_packing_encoding, ring = #ring_Z65537_i64_1_x8192, level = 1, scale = 1> : tensor<1024xi16> -> !pt
    preprocessing.store %pt, %0[] site 0<!pt> : !pt, <!pt>
    return %0 : !preprocessing.storage<!pt>
  }
  func.func @dot_product__preprocessed(%arg0: tensor<1x!ct_L2> {heir.kernel_info = {gap_factor = 1 : i64, result_shape = array<i64: 8>}, noise.bound = "28.00", tensor_ext.original_type = #tensor_ext.original_type<originalType = tensor<8xi16>, layout = #tensor_ext.layout<"{ [i0] -> [ct, slot] : ct = 0 and (-i0 + slot) mod 8 = 0 and 0 <= i0 <= 7 and 0 <= slot <= 1023 }">>}, %arg1: tensor<1x!ct_L2> {heir.kernel_info = {gap_factor = 1 : i64, result_shape = array<i64: 8>}, noise.bound = "28.00", tensor_ext.original_type = #tensor_ext.original_type<originalType = tensor<8xi16>, layout = #tensor_ext.layout<"{ [i0] -> [ct, slot] : ct = 0 and (-i0 + slot) mod 8 = 0 and 0 <= i0 <= 7 and 0 <= slot <= 1023 }">>}, %arg2: !preprocessing.storage<!pt>) -> tensor<1x!ct_L0> attributes {heir.interface = {func_name = "dot_product", roles = ["client.preprocessed", "server.evaluate"]}} {
    %c4 = arith.constant 4 : index
    %c2 = arith.constant 2 : index
    %c1 = arith.constant 1 : index
    %c0 = arith.constant 0 : index
    %extracted = tensor.extract %arg0[%c0] : tensor<1x!ct_L2>
    %extracted_0 = tensor.extract %arg1[%c0] : tensor<1x!ct_L2>
    %ct = bgv.mul %extracted, %extracted_0 {noise.bound = "69.00"} : (!ct_L2, !ct_L2) -> !ct_L2_D3
    %ct_1 = bgv.relinearize %ct <from_basis = [0, 1, 2], to_basis = [0, 1]> {noise.bound = "69.00"} : !ct_L2_D3 -> !ct_L2
    %ct_2 = bgv.rotate_cols %ct_1, %c1 : index {noise.bound = "69.00"} : !ct_L2
    %ct_3 = bgv.add %ct_1, %ct_2 {noise.bound = "70.00"} : (!ct_L2, !ct_L2) -> !ct_L2
    %ct_4 = bgv.rotate_cols %ct_3, %c2 : index {noise.bound = "70.00"} : !ct_L2
    %ct_5 = bgv.add %ct_3, %ct_4 {noise.bound = "71.00"} : (!ct_L2, !ct_L2) -> !ct_L2
    %ct_6 = bgv.rotate_cols %ct_5, %c4 : index {noise.bound = "71.00"} : !ct_L2
    %ct_7 = bgv.add %ct_5, %ct_6 {noise.bound = "72.00"} : (!ct_L2, !ct_L2) -> !ct_L2
    %ct_8 = bgv.modulus_switch %ct_7 <to_ring = #ring_rns_L1_1_x8192> {noise.bound = "28.09"} : !ct_L2 -> !ct_L1
    %pt = preprocessing.load %arg2[] site 0<!pt> : <!pt>, !pt
    %ct_9 = bgv.mul_plain %ct_8, %pt {noise.bound = "56.09"} : (!ct_L1, !pt) -> !ct_L1
    %0 = tensor.empty() : tensor<1x!ct_L0>
    %ct_10 = bgv.modulus_switch %ct_9 <to_ring = #ring_rns_L0_1_x8192> {noise.bound = "28.18"} : !ct_L1 -> !ct_L0
    %inserted = tensor.insert %ct_10 into %0[%c0] : tensor<1x!ct_L0>
    return %inserted : tensor<1x!ct_L0>
  }
  func.func @dot_product(%arg0: tensor<1x!ct_L2> {heir.kernel_info = {gap_factor = 1 : i64, result_shape = array<i64: 8>}, noise.bound = "28.00", tensor_ext.original_type = #tensor_ext.original_type<originalType = tensor<8xi16>, layout = #tensor_ext.layout<"{ [i0] -> [ct, slot] : ct = 0 and (-i0 + slot) mod 8 = 0 and 0 <= i0 <= 7 and 0 <= slot <= 1023 }">>}, %arg1: tensor<1x!ct_L2> {heir.kernel_info = {gap_factor = 1 : i64, result_shape = array<i64: 8>}, noise.bound = "28.00", tensor_ext.original_type = #tensor_ext.original_type<originalType = tensor<8xi16>, layout = #tensor_ext.layout<"{ [i0] -> [ct, slot] : ct = 0 and (-i0 + slot) mod 8 = 0 and 0 <= i0 <= 7 and 0 <= slot <= 1023 }">>}) -> (tensor<1x!ct_L0> {tensor_ext.original_type = #original_type}) attributes {heir.interface = {func_name = "dot_product", input_types = [tensor<8xi16>, tensor<8xi16>], result_types = [i16], roles = ["entry"]}} {
    %0 = call @dot_product__preprocessing() : () -> !preprocessing.storage<!pt>
    %1 = call @dot_product__preprocessed(%arg0, %arg1, %0) : (tensor<1x!ct_L2>, tensor<1x!ct_L2>, !preprocessing.storage<!pt>) -> tensor<1x!ct_L0>
    return %1 : tensor<1x!ct_L0>
  }
  func.func @dot_product__encrypt__arg0(%arg0: tensor<8xi16>, %pk: !pkey_L2) -> tensor<1x!ct_L2> attributes {heir.interface = {func_name = "dot_product", index = 0 : i64, roles = ["client.encrypt"]}} {
    %c0 = arith.constant 0 : index
    %c1024_i32 = arith.constant 1024 : i32
    %c8_i32 = arith.constant 8 : i32
    %cst = arith.constant dense<0> : tensor<1x1024xi16>
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %0 = scf.for %arg1 = %c0_i32 to %c8_i32 step %c1_i32 iter_args(%arg2 = %cst) -> (tensor<1x1024xi16>)  : i32 {
      %1 = arith.index_cast %arg1 : i32 to index
      %extracted = tensor.extract %arg0[%1] : tensor<8xi16>
      %2 = scf.for %arg3 = %arg1 to %c1024_i32 step %c8_i32 iter_args(%arg4 = %arg2) -> (tensor<1x1024xi16>)  : i32 {
        %3 = arith.index_cast %arg3 : i32 to index
        %inserted = tensor.insert %extracted into %arg4[%c0, %3] : tensor<1x1024xi16>
        scf.yield %inserted : tensor<1x1024xi16>
      }
      scf.yield %2 : tensor<1x1024xi16>
    }
    %extracted_slice = tensor.extract_slice %0[0, 0] [1, 1024] [1, 1] : tensor<1x1024xi16> to tensor<1024xi16>
    %pt = lwe.rlwe_encode %extracted_slice <encoding = #full_crt_packing_encoding, ring = #ring_Z65537_i64_1_x8192, level = 2, scale = 1> : tensor<1024xi16> -> !pt
    %ct = lwe.rlwe_encrypt %pt, %pk : (!pt, !pkey_L2) -> !ct_L2
    %from_elements = tensor.from_elements %ct : tensor<1x!ct_L2>
    return %from_elements : tensor<1x!ct_L2>
  }
  func.func @dot_product__encrypt__arg1(%arg0: tensor<8xi16>, %pk: !pkey_L2) -> tensor<1x!ct_L2> attributes {heir.interface = {func_name = "dot_product", index = 1 : i64, roles = ["client.encrypt"]}} {
    %c0 = arith.constant 0 : index
    %c1024_i32 = arith.constant 1024 : i32
    %c8_i32 = arith.constant 8 : i32
    %cst = arith.constant dense<0> : tensor<1x1024xi16>
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %0 = scf.for %arg1 = %c0_i32 to %c8_i32 step %c1_i32 iter_args(%arg2 = %cst) -> (tensor<1x1024xi16>)  : i32 {
      %1 = arith.index_cast %arg1 : i32 to index
      %extracted = tensor.extract %arg0[%1] : tensor<8xi16>
      %2 = scf.for %arg3 = %arg1 to %c1024_i32 step %c8_i32 iter_args(%arg4 = %arg2) -> (tensor<1x1024xi16>)  : i32 {
        %3 = arith.index_cast %arg3 : i32 to index
        %inserted = tensor.insert %extracted into %arg4[%c0, %3] : tensor<1x1024xi16>
        scf.yield %inserted : tensor<1x1024xi16>
      }
      scf.yield %2 : tensor<1x1024xi16>
    }
    %extracted_slice = tensor.extract_slice %0[0, 0] [1, 1024] [1, 1] : tensor<1x1024xi16> to tensor<1024xi16>
    %pt = lwe.rlwe_encode %extracted_slice <encoding = #full_crt_packing_encoding, ring = #ring_Z65537_i64_1_x8192, level = 2, scale = 1> : tensor<1024xi16> -> !pt
    %ct = lwe.rlwe_encrypt %pt, %pk : (!pt, !pkey_L2) -> !ct_L2
    %from_elements = tensor.from_elements %ct : tensor<1x!ct_L2>
    return %from_elements : tensor<1x!ct_L2>
  }
  func.func @dot_product__decrypt__result0(%arg0: tensor<1x!ct_L0>, %sk: !skey_L0) -> i16 attributes {heir.interface = {func_name = "dot_product", index = 0 : i64, roles = ["client.decrypt"]}} {
    %c0 = arith.constant 0 : index
    %extracted = tensor.extract %arg0[%c0] : tensor<1x!ct_L0>
    %pt = lwe.rlwe_decrypt %extracted, %sk : (!ct_L0, !skey_L0) -> !pt1
    %0 = lwe.rlwe_decode %pt <encoding = #full_crt_packing_encoding1, ring = #ring_Z65537_i64_1_x8192> : !pt1 -> tensor<1x1024xi16>
    %extracted_0 = tensor.extract %0[%c0, %c0] : tensor<1x1024xi16>
    return %extracted_0 : i16
  }
}

