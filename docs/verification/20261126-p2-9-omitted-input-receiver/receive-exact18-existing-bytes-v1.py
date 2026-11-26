import sys
sys.dont_write_bytecode = True
import base64
import datetime
import hashlib
import json
import os
import shutil
import stat
import tarfile
import urllib.request
from pathlib import Path, PurePosixPath

PIN = {'schema': 'p29_omitted_P2_byte_receiver_exact18_input_contract_v1', 'base': '/workspace/p29-omitted-inputs-20261126-b23868d', 'candidate_roots': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib'], 'objects': [{'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabBands', 'kind': 'native', 'provider': 'buchstab12', 'bytes': 1005224, 'sha256': '7af00b12866a5df8dc2da5157172281aa509182a2a321390d60db10588b43b23', 'original_object_path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBands.olean', 'object_member': 'objects/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBands.olean', 'source': None, 'provenance': {'index': {'bytes': 35907, 'sha256': 'ce7f66e7f392a9574ad8ed4cb03a6dd9451c17699f407ce7eddfc03eb83b6daf', 'git_blob': '65f2cb2a0aafffdca7bfc42d3c46478b2be5936f'}, 'transport_index': {'bytes': 12606, 'sha256': 'a0cc503bcf3666650cfe7fd33573ffbaf9c1aa099ec78dcc58b6e34fbf565be3', 'git_blob': 'b23868ddc9c0dd772b98bb1baa3546c15f2d0c48'}, 'root_transport_review': {'bytes': 2643, 'sha256': 'ecc73705d30291d29e5ab7207477fb775f39521037b7b09556fbba3ec5419949', 'git_blob': '3bad85bf16f74ce52036bdef692a738e10badb56'}, 'formal_source_not_transferred_by_this_object_only_archive': True}, 'destination_relative': 'lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBands.olean', 'P2_candidates': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBands.olean', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBands.olean']}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabBase', 'kind': 'native', 'provider': 'buchstab12', 'bytes': 495736, 'sha256': 'bdb45e61412726782fc7801b23f786f8436a763d94330223c38c698e49137979', 'original_object_path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBase.olean', 'object_member': 'objects/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBase.olean', 'source': None, 'provenance': {'index': {'bytes': 35907, 'sha256': 'ce7f66e7f392a9574ad8ed4cb03a6dd9451c17699f407ce7eddfc03eb83b6daf', 'git_blob': '65f2cb2a0aafffdca7bfc42d3c46478b2be5936f'}, 'transport_index': {'bytes': 12606, 'sha256': 'a0cc503bcf3666650cfe7fd33573ffbaf9c1aa099ec78dcc58b6e34fbf565be3', 'git_blob': 'b23868ddc9c0dd772b98bb1baa3546c15f2d0c48'}, 'root_transport_review': {'bytes': 2643, 'sha256': 'ecc73705d30291d29e5ab7207477fb775f39521037b7b09556fbba3ec5419949', 'git_blob': '3bad85bf16f74ce52036bdef692a738e10badb56'}, 'formal_source_not_transferred_by_this_object_only_archive': True}, 'destination_relative': 'lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBase.olean', 'P2_candidates': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBase.olean', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBase.olean']}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabBaseEstimate', 'kind': 'native', 'provider': 'buchstab12', 'bytes': 302232, 'sha256': 'a0ed17870cc9b34aa77cc1eacc96380f26a136e98f5aba1a8f5e70418b0ff195', 'original_object_path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBaseEstimate.olean', 'object_member': 'objects/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBaseEstimate.olean', 'source': None, 'provenance': {'index': {'bytes': 35907, 'sha256': 'ce7f66e7f392a9574ad8ed4cb03a6dd9451c17699f407ce7eddfc03eb83b6daf', 'git_blob': '65f2cb2a0aafffdca7bfc42d3c46478b2be5936f'}, 'transport_index': {'bytes': 12606, 'sha256': 'a0cc503bcf3666650cfe7fd33573ffbaf9c1aa099ec78dcc58b6e34fbf565be3', 'git_blob': 'b23868ddc9c0dd772b98bb1baa3546c15f2d0c48'}, 'root_transport_review': {'bytes': 2643, 'sha256': 'ecc73705d30291d29e5ab7207477fb775f39521037b7b09556fbba3ec5419949', 'git_blob': '3bad85bf16f74ce52036bdef692a738e10badb56'}, 'formal_source_not_transferred_by_this_object_only_archive': True}, 'destination_relative': 'lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBaseEstimate.olean', 'P2_candidates': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBaseEstimate.olean', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBaseEstimate.olean']}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabBounds', 'kind': 'native', 'provider': 'buchstab12', 'bytes': 417864, 'sha256': '40e6739d0928ae2c70deca8b80307dd87595f0076c851e4a2cf9e0098a749b75', 'original_object_path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBounds.olean', 'object_member': 'objects/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBounds.olean', 'source': None, 'provenance': {'index': {'bytes': 35907, 'sha256': 'ce7f66e7f392a9574ad8ed4cb03a6dd9451c17699f407ce7eddfc03eb83b6daf', 'git_blob': '65f2cb2a0aafffdca7bfc42d3c46478b2be5936f'}, 'transport_index': {'bytes': 12606, 'sha256': 'a0cc503bcf3666650cfe7fd33573ffbaf9c1aa099ec78dcc58b6e34fbf565be3', 'git_blob': 'b23868ddc9c0dd772b98bb1baa3546c15f2d0c48'}, 'root_transport_review': {'bytes': 2643, 'sha256': 'ecc73705d30291d29e5ab7207477fb775f39521037b7b09556fbba3ec5419949', 'git_blob': '3bad85bf16f74ce52036bdef692a738e10badb56'}, 'formal_source_not_transferred_by_this_object_only_archive': True}, 'destination_relative': 'lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBounds.olean', 'P2_candidates': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBounds.olean', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBounds.olean']}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabCount', 'kind': 'native', 'provider': 'buchstab12', 'bytes': 215320, 'sha256': '539aa96f95335718ebeaab8c69e9cdbdd5d00d7c929e8c61909592dfff628d7d', 'original_object_path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabCount.olean', 'object_member': 'objects/MathlibNt/SieveTheory/LiLiuPrereqBuchstabCount.olean', 'source': None, 'provenance': {'index': {'bytes': 35907, 'sha256': 'ce7f66e7f392a9574ad8ed4cb03a6dd9451c17699f407ce7eddfc03eb83b6daf', 'git_blob': '65f2cb2a0aafffdca7bfc42d3c46478b2be5936f'}, 'transport_index': {'bytes': 12606, 'sha256': 'a0cc503bcf3666650cfe7fd33573ffbaf9c1aa099ec78dcc58b6e34fbf565be3', 'git_blob': 'b23868ddc9c0dd772b98bb1baa3546c15f2d0c48'}, 'root_transport_review': {'bytes': 2643, 'sha256': 'ecc73705d30291d29e5ab7207477fb775f39521037b7b09556fbba3ec5419949', 'git_blob': '3bad85bf16f74ce52036bdef692a738e10badb56'}, 'formal_source_not_transferred_by_this_object_only_archive': True}, 'destination_relative': 'lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabCount.olean', 'P2_candidates': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabCount.olean', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabCount.olean']}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabFunction', 'kind': 'native', 'provider': 'buchstab12', 'bytes': 313800, 'sha256': 'f78a815dea0aad0833aac831dc2233cdcd3fd5c7681d6220be3b253786b1b5ee', 'original_object_path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabFunction.olean', 'object_member': 'objects/MathlibNt/SieveTheory/LiLiuPrereqBuchstabFunction.olean', 'source': None, 'provenance': {'index': {'bytes': 35907, 'sha256': 'ce7f66e7f392a9574ad8ed4cb03a6dd9451c17699f407ce7eddfc03eb83b6daf', 'git_blob': '65f2cb2a0aafffdca7bfc42d3c46478b2be5936f'}, 'transport_index': {'bytes': 12606, 'sha256': 'a0cc503bcf3666650cfe7fd33573ffbaf9c1aa099ec78dcc58b6e34fbf565be3', 'git_blob': 'b23868ddc9c0dd772b98bb1baa3546c15f2d0c48'}, 'root_transport_review': {'bytes': 2643, 'sha256': 'ecc73705d30291d29e5ab7207477fb775f39521037b7b09556fbba3ec5419949', 'git_blob': '3bad85bf16f74ce52036bdef692a738e10badb56'}, 'formal_source_not_transferred_by_this_object_only_archive': True}, 'destination_relative': 'lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabFunction.olean', 'P2_candidates': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabFunction.olean', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabFunction.olean']}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabIntegral', 'kind': 'native', 'provider': 'buchstab12', 'bytes': 355112, 'sha256': '812cb313a21b538c183715b1b829d286628fd30a8a067ca43fb915a54b9a083b', 'original_object_path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabIntegral.olean', 'object_member': 'objects/MathlibNt/SieveTheory/LiLiuPrereqBuchstabIntegral.olean', 'source': None, 'provenance': {'index': {'bytes': 35907, 'sha256': 'ce7f66e7f392a9574ad8ed4cb03a6dd9451c17699f407ce7eddfc03eb83b6daf', 'git_blob': '65f2cb2a0aafffdca7bfc42d3c46478b2be5936f'}, 'transport_index': {'bytes': 12606, 'sha256': 'a0cc503bcf3666650cfe7fd33573ffbaf9c1aa099ec78dcc58b6e34fbf565be3', 'git_blob': 'b23868ddc9c0dd772b98bb1baa3546c15f2d0c48'}, 'root_transport_review': {'bytes': 2643, 'sha256': 'ecc73705d30291d29e5ab7207477fb775f39521037b7b09556fbba3ec5419949', 'git_blob': '3bad85bf16f74ce52036bdef692a738e10badb56'}, 'formal_source_not_transferred_by_this_object_only_archive': True}, 'destination_relative': 'lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabIntegral.olean', 'P2_candidates': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabIntegral.olean', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabIntegral.olean']}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabPNT', 'kind': 'native', 'provider': 'buchstab12', 'bytes': 239240, 'sha256': '1f48755c44eadce94bfd62332f1ca9c8892aefd7692a34407ecbcdb8350bcaef', 'original_object_path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabPNT.olean', 'object_member': 'objects/MathlibNt/SieveTheory/LiLiuPrereqBuchstabPNT.olean', 'source': None, 'provenance': {'index': {'bytes': 35907, 'sha256': 'ce7f66e7f392a9574ad8ed4cb03a6dd9451c17699f407ce7eddfc03eb83b6daf', 'git_blob': '65f2cb2a0aafffdca7bfc42d3c46478b2be5936f'}, 'transport_index': {'bytes': 12606, 'sha256': 'a0cc503bcf3666650cfe7fd33573ffbaf9c1aa099ec78dcc58b6e34fbf565be3', 'git_blob': 'b23868ddc9c0dd772b98bb1baa3546c15f2d0c48'}, 'root_transport_review': {'bytes': 2643, 'sha256': 'ecc73705d30291d29e5ab7207477fb775f39521037b7b09556fbba3ec5419949', 'git_blob': '3bad85bf16f74ce52036bdef692a738e10badb56'}, 'formal_source_not_transferred_by_this_object_only_archive': True}, 'destination_relative': 'lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabPNT.olean', 'P2_candidates': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabPNT.olean', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabPNT.olean']}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabPrimeSums', 'kind': 'native', 'provider': 'buchstab12', 'bytes': 708360, 'sha256': '85e0756e603bb8b5e51b87247b989a3eb0a7c0c25c9b6dfb1e786ebf2fbca739', 'original_object_path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabPrimeSums.olean', 'object_member': 'objects/MathlibNt/SieveTheory/LiLiuPrereqBuchstabPrimeSums.olean', 'source': None, 'provenance': {'index': {'bytes': 35907, 'sha256': 'ce7f66e7f392a9574ad8ed4cb03a6dd9451c17699f407ce7eddfc03eb83b6daf', 'git_blob': '65f2cb2a0aafffdca7bfc42d3c46478b2be5936f'}, 'transport_index': {'bytes': 12606, 'sha256': 'a0cc503bcf3666650cfe7fd33573ffbaf9c1aa099ec78dcc58b6e34fbf565be3', 'git_blob': 'b23868ddc9c0dd772b98bb1baa3546c15f2d0c48'}, 'root_transport_review': {'bytes': 2643, 'sha256': 'ecc73705d30291d29e5ab7207477fb775f39521037b7b09556fbba3ec5419949', 'git_blob': '3bad85bf16f74ce52036bdef692a738e10badb56'}, 'formal_source_not_transferred_by_this_object_only_archive': True}, 'destination_relative': 'lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabPrimeSums.olean', 'P2_candidates': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabPrimeSums.olean', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabPrimeSums.olean']}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabUniform', 'kind': 'native', 'provider': 'buchstab12', 'bytes': 452912, 'sha256': '326ca610964a3a6b2659cd4230681c266abbeb48c7b1fc0fcca322f33c592d90', 'original_object_path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniform.olean', 'object_member': 'objects/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniform.olean', 'source': None, 'provenance': {'index': {'bytes': 35907, 'sha256': 'ce7f66e7f392a9574ad8ed4cb03a6dd9451c17699f407ce7eddfc03eb83b6daf', 'git_blob': '65f2cb2a0aafffdca7bfc42d3c46478b2be5936f'}, 'transport_index': {'bytes': 12606, 'sha256': 'a0cc503bcf3666650cfe7fd33573ffbaf9c1aa099ec78dcc58b6e34fbf565be3', 'git_blob': 'b23868ddc9c0dd772b98bb1baa3546c15f2d0c48'}, 'root_transport_review': {'bytes': 2643, 'sha256': 'ecc73705d30291d29e5ab7207477fb775f39521037b7b09556fbba3ec5419949', 'git_blob': '3bad85bf16f74ce52036bdef692a738e10badb56'}, 'formal_source_not_transferred_by_this_object_only_archive': True}, 'destination_relative': 'lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniform.olean', 'P2_candidates': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniform.olean', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniform.olean']}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabUniformAbel', 'kind': 'native', 'provider': 'buchstab12', 'bytes': 1921552, 'sha256': '0891f3fa7c30839054029fa5b2b3d28b116a9bddb8a74e2207d223913ff0b368', 'original_object_path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniformAbel.olean', 'object_member': 'objects/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniformAbel.olean', 'source': None, 'provenance': {'index': {'bytes': 35907, 'sha256': 'ce7f66e7f392a9574ad8ed4cb03a6dd9451c17699f407ce7eddfc03eb83b6daf', 'git_blob': '65f2cb2a0aafffdca7bfc42d3c46478b2be5936f'}, 'transport_index': {'bytes': 12606, 'sha256': 'a0cc503bcf3666650cfe7fd33573ffbaf9c1aa099ec78dcc58b6e34fbf565be3', 'git_blob': 'b23868ddc9c0dd772b98bb1baa3546c15f2d0c48'}, 'root_transport_review': {'bytes': 2643, 'sha256': 'ecc73705d30291d29e5ab7207477fb775f39521037b7b09556fbba3ec5419949', 'git_blob': '3bad85bf16f74ce52036bdef692a738e10badb56'}, 'formal_source_not_transferred_by_this_object_only_archive': True}, 'destination_relative': 'lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniformAbel.olean', 'P2_candidates': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniformAbel.olean', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniformAbel.olean']}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabUniformFixedCompat', 'kind': 'native', 'provider': 'buchstab12', 'bytes': 1339680, 'sha256': '71575dea300b4d15714d5c92392589faed3542cc3ee13a51284dbb6e0eb9faa1', 'original_object_path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniformFixedCompat.olean', 'object_member': 'objects/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniformFixedCompat.olean', 'source': None, 'provenance': {'index': {'bytes': 35907, 'sha256': 'ce7f66e7f392a9574ad8ed4cb03a6dd9451c17699f407ce7eddfc03eb83b6daf', 'git_blob': '65f2cb2a0aafffdca7bfc42d3c46478b2be5936f'}, 'transport_index': {'bytes': 12606, 'sha256': 'a0cc503bcf3666650cfe7fd33573ffbaf9c1aa099ec78dcc58b6e34fbf565be3', 'git_blob': 'b23868ddc9c0dd772b98bb1baa3546c15f2d0c48'}, 'root_transport_review': {'bytes': 2643, 'sha256': 'ecc73705d30291d29e5ab7207477fb775f39521037b7b09556fbba3ec5419949', 'git_blob': '3bad85bf16f74ce52036bdef692a738e10badb56'}, 'formal_source_not_transferred_by_this_object_only_archive': True}, 'destination_relative': 'lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniformFixedCompat.olean', 'P2_candidates': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniformFixedCompat.olean', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniformFixedCompat.olean']}, {'module': 'MathlibNt.Wu2008DoubleSieve.NonunitRoughUniform', 'kind': 'native', 'provider': 'nonunit44', 'bytes': 320080, 'sha256': 'd5dcdada890ec4dc434a88a504b217db32372af941be97b722cb077116e3dc5f', 'original_object_path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/Wu2008DoubleSieve/NonunitRoughUniform.olean', 'object_member': 'native-assets/.lake/build/lib/lean/MathlibNt/Wu2008DoubleSieve/NonunitRoughUniform.olean', 'source': {'provider': 'nonunit44', 'member': 'native-assets/MathlibNt/Wu2008DoubleSieve/NonunitRoughUniform.lean', 'bytes': 4349, 'sha256': '5e97e0faa5f088407cf64c8a46aaea191f8f7c62aa959f92aadd29deb10c3102'}, 'provenance': {'native14_index': {'bytes': 35907, 'sha256': 'ce7f66e7f392a9574ad8ed4cb03a6dd9451c17699f407ce7eddfc03eb83b6daf', 'git_blob': '65f2cb2a0aafffdca7bfc42d3c46478b2be5936f'}, 'original_transport': {'bytes': 6412, 'sha256': 'f0b93773417cba1df5c5587ce54ebb32105db90f3b043dee81696c2561ebfd58', 'git_blob': '4a919c8a8fb8c5044c5d2b69cb14bf8e1f395abe'}, 'original_manifest': {'bytes': 8383, 'sha256': '0780beabbd67410fc72275b3a0bd1c5907ed5822eb90999b3cb33cf58bc095b9', 'git_blob': '00995249f324606b6a33b376df0948abd6694236'}, 'old_owned_counts_referenced_only': {'Core': 19, 'Upper': 11}, 'new_qualification_credit': 0}, 'destination_relative': 'lib/lean/MathlibNt/Wu2008DoubleSieve/NonunitRoughUniform.olean', 'P2_candidates': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib/MathlibNt/Wu2008DoubleSieve/NonunitRoughUniform.olean', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/MathlibNt/Wu2008DoubleSieve/NonunitRoughUniform.olean']}, {'module': 'MathlibNt.Wu2008DoubleSieve.NonunitRoughUniformCore', 'kind': 'native', 'provider': 'nonunit44', 'bytes': 379328, 'sha256': 'eb25d766e699e3e43d931758b0aa55a15d8da89b48f256bbee26064e7202713b', 'original_object_path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/Wu2008DoubleSieve/NonunitRoughUniformCore.olean', 'object_member': 'native-assets/.lake/build/lib/lean/MathlibNt/Wu2008DoubleSieve/NonunitRoughUniformCore.olean', 'source': {'provider': 'nonunit44', 'member': 'native-assets/MathlibNt/Wu2008DoubleSieve/NonunitRoughUniformCore.lean', 'bytes': 4613, 'sha256': 'c420a5a06e8735eca6143b786dd71629c101c8af6041642f14dbdfc45cd2f853'}, 'provenance': {'native14_index': {'bytes': 35907, 'sha256': 'ce7f66e7f392a9574ad8ed4cb03a6dd9451c17699f407ce7eddfc03eb83b6daf', 'git_blob': '65f2cb2a0aafffdca7bfc42d3c46478b2be5936f'}, 'original_transport': {'bytes': 6412, 'sha256': 'f0b93773417cba1df5c5587ce54ebb32105db90f3b043dee81696c2561ebfd58', 'git_blob': '4a919c8a8fb8c5044c5d2b69cb14bf8e1f395abe'}, 'original_manifest': {'bytes': 8383, 'sha256': '0780beabbd67410fc72275b3a0bd1c5907ed5822eb90999b3cb33cf58bc095b9', 'git_blob': '00995249f324606b6a33b376df0948abd6694236'}, 'old_owned_counts_referenced_only': {'Core': 19, 'Upper': 11}, 'new_qualification_credit': 0}, 'destination_relative': 'lib/lean/MathlibNt/Wu2008DoubleSieve/NonunitRoughUniformCore.olean', 'P2_candidates': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib/MathlibNt/Wu2008DoubleSieve/NonunitRoughUniformCore.olean', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/MathlibNt/Wu2008DoubleSieve/NonunitRoughUniformCore.olean']}, {'module': 'ImbalancedChen.P2MarkedPrimeProductFibreCore', 'kind': 'foreign_project', 'provider': 'unit128', 'bytes': 151912, 'sha256': '7b54021ff39a596a2ab8085ee89c827c77f181e04acc7bb616d193b62b5e2cfa', 'object_member': 'project/.lake/build/lib/lean/ImbalancedChen/P2MarkedPrimeProductFibreCore.olean', 'source': {'provider': 'unit128', 'member': 'verification/borrowed-sources/ImbalancedChen/P2MarkedPrimeProductFibreCore.lean', 'bytes': 4267, 'sha256': 'ca2a53a58e6f6c858c513dbead63ae469c193f2b0760c2e0dd529144f53563bf'}, 'provenance': {'original_archive_index': {'bytes': 11341, 'sha256': '25792a0b27c5d9204a4b521e6b92bb690db9aead1890fb655c519bd4f7585554', 'git_blob': '5ef6ca4bd4e2cb969eed630edeb48f5553ab4946'}, 'root_acceptance_commit': '1a6a41c6a5a0240b3c21b01f3b4782b436c05b98', 'root_acceptance_path': 'docs/verification/20261126-p2-9-unit-tail-count/ROOT_ACCEPTANCE.json', 'original_borrow_record': {'module': 'ImbalancedChen.P2MarkedPrimeProductFibreCore', 'source': '/workspace/p29-unit-tail-20261126-8131f7d6/verification/borrowed-sources/ImbalancedChen/P2MarkedPrimeProductFibreCore.lean', 'source_sha256': 'ca2a53a58e6f6c858c513dbead63ae469c193f2b0760c2e0dd529144f53563bf', 'source_bytes': 4267, 'object': '/workspace/p29-unit-tail-20261126-8131f7d6/project/.lake/build/lib/lean/ImbalancedChen/P2MarkedPrimeProductFibreCore.olean', 'object_sha256': '7b54021ff39a596a2ab8085ee89c827c77f181e04acc7bb616d193b62b5e2cfa', 'object_bytes': 151912, 'original_source': '/workspace/p29-unit-tail-20261126-8131f7d6/suppliers/fibre-tuple/project/ImbalancedChen/P2MarkedPrimeProductFibreCore.lean', 'original_object': '/workspace/p29-unit-tail-20261126-8131f7d6/suppliers/fibre-tuple/project/.lake/build/lib/lean/ImbalancedChen/P2MarkedPrimeProductFibreCore.olean', 'authority': 'accepted_P1_fibre_core', 'producer': {'job': 'job_f761e0d8b28e47369e915aa7d21f3347', 'source_blob': '3b7247d17ee09c52e825973f42333c30745f054f', 'source_sha256': 'ca2a53a58e6f6c858c513dbead63ae469c193f2b0760c2e0dd529144f53563bf', 'normal_process_path': '/workspace/p29-radial-verification-20261125/fibre-tuple-attempt-1/normal-build-process.json', 'normal_process_sha256': 'cb76ae44354ced28f5733eed2b806ce46f36d76218270c439cf65b6deefa9de6', 'normal_log_sha256': '4dad003d7823a3a61353b6ad37cbebd7425f00e9410ed505cec9840d113cd6c2', 'source_and_outputs': {'/workspace/p29-radial-20261125/ImbalancedChen/P2MarkedPrimeProductFibreCore.lean': {'bytes': 4267, 'sha256': 'ca2a53a58e6f6c858c513dbead63ae469c193f2b0760c2e0dd529144f53563bf'}, '/workspace/p29-radial-20261125/.lake/build/lib/lean/ImbalancedChen/P2MarkedPrimeProductFibreCore.olean': {'bytes': 151912, 'sha256': '7b54021ff39a596a2ab8085ee89c827c77f181e04acc7bb616d193b62b5e2cfa'}, '/workspace/p29-radial-20261125/.lake/build/lib/lean/ImbalancedChen/P2MarkedPrimeProductFibreCore.ilean': {'bytes': 16000, 'sha256': '63b620daa364f8441495fb011df55fa58ddf126e07970441812cdf768ab74094'}, '/workspace/p29-radial-20261125/.lake/build/lib/lean/ImbalancedChen/P2MarkedPrimeProductFibreCore.trace': {'bytes': 3440, 'sha256': '08fb06ffb1119cf5a0c8b535acd9bc6ceb37e8bc38027f3c13c48847a4e82cb2'}, '/workspace/p29-radial-20261125/.lake/build/ir/ImbalancedChen/P2MarkedPrimeProductFibreCore.c': {'bytes': 32884, 'sha256': '297ffab7de1cc874c2ca57829d2ca6be047ac7055a00213a44d1e8157a776465'}, '/workspace/p29-radial-20261125/.lake/build/ir/ImbalancedChen/P2MarkedPrimeProductFibreCore.setup.json': {'bytes': 551580, 'sha256': '942946bd34a74c63474277b481fe6fbcd385bf44f61b0158b4a0c41fef6b4b31'}}, 'new_source_compilation_for_core_allowed': False}, 'copied_original_facets': ['.olean'], 'new_source_compilation': False, 'direct_project_imports': []}, 'original_qualification_reference': {'member': 'verification/SUPPLY_QUALIFICATION.json', 'bytes': 40177, 'sha256': '1d63ecbcc0a21300314d26b8493d6ed07d30d622c745e1ffc1956bf10b324a21', 'status': 'PASS_CURRENT_P3_BOUND_IMPORTS_NAMED_KERNEL_FULL_OWNED', 'old_modules': 18, 'old_owned': 394, 'named_kernel_exit': 0, 'full_owned_exit': 0, 'actual_input_graph_member': 'verification/borrowed-actual-imports-bindings.json', 'actual_input_graph': {'bytes': 27062843, 'sha256': '6b0e29d00cf57429278bb0416c62f8642c15738a80c61bd4e0dd0b31513c2659'}}, 'new_qualification_credit': 0}, 'destination_relative': 'lib/lean/ImbalancedChen/P2MarkedPrimeProductFibreCore.olean', 'P2_candidates': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib/ImbalancedChen/P2MarkedPrimeProductFibreCore.olean', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/ImbalancedChen/P2MarkedPrimeProductFibreCore.olean']}, {'module': 'ImbalancedChen.P2FiniteMarkedGamma5FrozenConstants', 'kind': 'foreign_project', 'provider': 'unit128', 'bytes': 27672, 'sha256': '453214cece45bee1398a74e5fa8137df2366f2a37dad3d151b10825ee0915907', 'object_member': 'project/.lake/build/lib/lean/ImbalancedChen/P2FiniteMarkedGamma5FrozenConstants.olean', 'source': {'provider': 'unit128', 'member': 'verification/borrowed-sources/ImbalancedChen/P2FiniteMarkedGamma5FrozenConstants.lean', 'bytes': 1343, 'sha256': 'fb5cb2655a7907efb595a5e51ec87d1f3f0ce846316e65564e0e1a1a2e0ba093'}, 'provenance': {'original_archive_index': {'bytes': 11341, 'sha256': '25792a0b27c5d9204a4b521e6b92bb690db9aead1890fb655c519bd4f7585554', 'git_blob': '5ef6ca4bd4e2cb969eed630edeb48f5553ab4946'}, 'root_acceptance_commit': '1a6a41c6a5a0240b3c21b01f3b4782b436c05b98', 'root_acceptance_path': 'docs/verification/20261126-p2-9-unit-tail-count/ROOT_ACCEPTANCE.json', 'original_borrow_record': {'module': 'ImbalancedChen.P2FiniteMarkedGamma5FrozenConstants', 'source': '/workspace/p29-unit-tail-20261126-8131f7d6/verification/borrowed-sources/ImbalancedChen/P2FiniteMarkedGamma5FrozenConstants.lean', 'source_sha256': 'fb5cb2655a7907efb595a5e51ec87d1f3f0ce846316e65564e0e1a1a2e0ba093', 'source_bytes': 1343, 'object': '/workspace/p29-unit-tail-20261126-8131f7d6/project/.lake/build/lib/lean/ImbalancedChen/P2FiniteMarkedGamma5FrozenConstants.olean', 'object_sha256': '453214cece45bee1398a74e5fa8137df2366f2a37dad3d151b10825ee0915907', 'object_bytes': 27672, 'original_source': '/workspace/p29-unit-tail-20261126-8131f7d6/suppliers/radial-three/p29-radial-three-qualified-20261125/project/ImbalancedChen/P2FiniteMarkedGamma5FrozenConstants.lean', 'original_object': '/workspace/p29-unit-tail-20261126-8131f7d6/suppliers/radial-three/p29-radial-three-qualified-20261125/project/.lake/build/lib/lean/ImbalancedChen/P2FiniteMarkedGamma5FrozenConstants.olean', 'authority': 'accepted_P1_frozen_constants', 'producer': {'archive_blob': '5e4b535bbbd7fc5041c7cf2c47831ce50b5fbaf1', 'archive_sha256': '4e6e5ecb0af9ddba5d42719b11440e1c14fc8ed408245f8f005eef02b40f718c', 'validation_sha256': 'cfd743edf49b26a995a4d86f22c1d74f3440326cfeb5004d4843f27f00d4daf2'}, 'copied_original_facets': ['.olean'], 'new_source_compilation': False, 'direct_project_imports': []}, 'original_qualification_reference': {'member': 'verification/SUPPLY_QUALIFICATION.json', 'bytes': 40177, 'sha256': '1d63ecbcc0a21300314d26b8493d6ed07d30d622c745e1ffc1956bf10b324a21', 'status': 'PASS_CURRENT_P3_BOUND_IMPORTS_NAMED_KERNEL_FULL_OWNED', 'old_modules': 18, 'old_owned': 394, 'named_kernel_exit': 0, 'full_owned_exit': 0, 'actual_input_graph_member': 'verification/borrowed-actual-imports-bindings.json', 'actual_input_graph': {'bytes': 27062843, 'sha256': '6b0e29d00cf57429278bb0416c62f8642c15738a80c61bd4e0dd0b31513c2659'}}, 'new_qualification_credit': 0}, 'destination_relative': 'lib/lean/ImbalancedChen/P2FiniteMarkedGamma5FrozenConstants.olean', 'P2_candidates': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib/ImbalancedChen/P2FiniteMarkedGamma5FrozenConstants.olean', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/ImbalancedChen/P2FiniteMarkedGamma5FrozenConstants.olean']}, {'module': 'ImbalancedChen.P2FiniteMarkedGamma5NonunitQuotient', 'kind': 'foreign_project', 'provider': 'standalone_git', 'git_blob': 'be40b1d4d962e849be5018a7d8b22241d699818d', 'bytes': 210800, 'sha256': '86ade819d9ae33358ea6ea00b419c4ddfb6727b28637145c45b1ca412a849eb8', 'source': {'provider': 'standalone_git', 'git_blob': 'eeaf7a2c714da44928cc43e79780846e1e72d23b', 'bytes': 3431, 'sha256': '42de161d084cac904775203fb0188bcc7bc5459a9b230b53c5c405e692262d77'}, 'provenance': {'root_review': {'bytes': 3839, 'sha256': '49b8d37858e3e747067c38accfbbca10458f86f61b1bc273b09578954a5f9296', 'git_blob': 'cdf0f61bd037bca3f295d407db6e5019a12d6e5c'}, 'root_acceptance_commit': '952caa6e5bb055bb5a4ed87d1d9855de36e4b35a', 'root_acceptance_path': 'docs/verification/20261126-p2-9-nonunit-quotient/ROOT_ACCEPTANCE.json', 'original_owned_count_referenced_only': 17, 'new_qualification_credit': 0}, 'destination_relative': 'lib/lean/ImbalancedChen/P2FiniteMarkedGamma5NonunitQuotient.olean', 'P2_candidates': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib/ImbalancedChen/P2FiniteMarkedGamma5NonunitQuotient.olean', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/ImbalancedChen/P2FiniteMarkedGamma5NonunitQuotient.olean']}, {'module': 'ImbalancedChen.P2FiniteMarkedGamma5RadialRoughMass', 'kind': 'foreign_project', 'provider': 'standalone_git', 'bytes': 498736, 'sha256': '9c70ee9877b4b6158220d8b871cb8f240082958cc61f1770bb77a4fcbaa3486a', 'git_blob': '6988923383bdf7eb99cd2777ce033f86aafc4e1d', 'source': {'provider': 'standalone_git', 'bytes': 9367, 'sha256': '7766fbca185e25e7380aee84e805cd3c35b94daaa8e6f7f98740ee3533fb67eb', 'git_blob': 'aca4621da617c19221048a7d8d11f0b22694ee09'}, 'provenance': {'existing_object_reception': {'bytes': 14657, 'sha256': '343cd864d6d5736e5a6155cf4b87bd5603c0d4d3b5ff2f306c878877ea3a2e91', 'git_blob': '2d1f65599fd058d7db3ed287a9fdf59877cc7b69'}, 'original_object_path': '/workspace/p29-nonunit-quotient-20261126-0117dd4/.lake/build/lib/lean/ImbalancedChen/P2FiniteMarkedGamma5RadialRoughMass.olean', 'original_transfer_task': 'job_32632f36078d4775bd171830bd662e7f', 'new_qualification_credit': 0}, 'destination_relative': 'lib/lean/ImbalancedChen/P2FiniteMarkedGamma5RadialRoughMass.olean', 'P2_candidates': ['/workspace/p2-saving16-20261125/.lake/p2-private/lib/ImbalancedChen/P2FiniteMarkedGamma5RadialRoughMass.olean', '/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/ImbalancedChen/P2FiniteMarkedGamma5RadialRoughMass.olean']}], 'archives': [{'id': 'buchstab12', 'archive': {'bytes': 1657884, 'sha256': '626152e850c142897b9b02902b8e75b3f7d9f5e5ab67371656bdca531c8f89f0'}, 'parts': [{'bytes': 400000, 'git_blob': '356ce981ef43e2d25cf2c4a8ad3a714f4b50d5a6', 'index': 0, 'offset': 0, 'sha256': '42700ae060cce04e32e1f8768722a30c6a21d9f84b2646f99863b6b1baeb0282'}, {'bytes': 400000, 'git_blob': '5e0b3e4bcdfc3aa3174a4b24281ce938c369a630', 'index': 1, 'offset': 400000, 'sha256': 'd63d6bf76dd2f8cd1c7b5a1ee23e5a0f32be1e06008e06c6a0c834fe54f9684f'}, {'bytes': 400000, 'git_blob': 'de67e6be7f8f3f7c548f7900b8b129b23e6c64a3', 'index': 2, 'offset': 800000, 'sha256': '5c0d081502cc2c1531d29145ec80e2bc872cc6f54e591128024e9d71a246762a'}, {'bytes': 400000, 'git_blob': '2e1f1aa826b7d9a212c9e828266a1e5bb6bf6db9', 'index': 3, 'offset': 1200000, 'sha256': 'aed2fa37ad47c75e198a0b407435c9261e5aa7c74ec23c5bd751f4f00e32ca84'}, {'bytes': 57884, 'git_blob': 'd2bbb4605da04773d284ad0edcb0826d38f1d8ca', 'index': 4, 'offset': 1600000, 'sha256': 'd985a8d64a5839fde5601883cc3eaef1aca086ae8b7bf32f19d6fd70cc0aaed0'}], 'member_count': 16, 'expanded_member_bytes': 7819675, 'manifest': {'member': 'FILE_MANIFEST.json', 'shape': 'direct_dictionary', 'bytes': 3428, 'sha256': 'b11c49e9c0cb49631f452fd496f440d78b36b10a03748dcfb33fd7ffedc80d52'}}, {'id': 'nonunit44', 'archive': {'bytes': 1371952, 'sha256': 'c9f0734846b9b79b5a6e8405f9a732c66e54adf1388c92ff417c534150e3ccbf'}, 'parts': [{'index': 0, 'offset': 0, 'bytes': 180000, 'sha256': '09a132669420e2497d0cddd1122fcc7b3924160576fb21416db36fd27a41149d', 'git_blob': '65430d3561699bd4e485ec25fb19b2102a9e3f5c'}, {'index': 1, 'offset': 180000, 'bytes': 180000, 'sha256': '0e39d8998a1c44d2e101313e57146cdd35f9166180cb263ccd8f18f30e2a8818', 'git_blob': '4e528ccb40cc8f6a22195f093d7b68f7c6c47d85'}, {'index': 2, 'offset': 360000, 'bytes': 180000, 'sha256': 'dc3f2068eb4c3cb0aab9f4025c8e687a3aa9a0804591e91c0a17db1b822e2b5f', 'git_blob': '5c4ec6a053fe6ccd289f417969beef5ed78221b7'}, {'index': 3, 'offset': 540000, 'bytes': 180000, 'sha256': 'cb00710c72fd50ae37db92bf1b5208823e5e358c85224cb877303b188ae56e48', 'git_blob': 'f0cf48579a8181a6c778bc55f581b969b6db5095'}, {'index': 4, 'offset': 720000, 'bytes': 180000, 'sha256': '6f8ebb0f1d77efb249b18ecea0c72f222e3515547428ddaf5dcc0d1fb734c868', 'git_blob': 'c7fd5e0ca1cfcc7568c3b192091619c5630d0f3c'}, {'index': 5, 'offset': 900000, 'bytes': 180000, 'sha256': '099074259029f0ff11c52a2ae80c6e72504e426e90531792d6c4fe2511f533bc', 'git_blob': '8c728d9ce40ebebba5549307030f9cfed1a893ae'}, {'index': 6, 'offset': 1080000, 'bytes': 180000, 'sha256': 'fd867b80d714422e4d0a0ab011726df7d891150fb966b3874538c74fa873fa4f', 'git_blob': 'f0a3a2a0fc63e1d1d21803f770537d27cbbaad93'}, {'index': 7, 'offset': 1260000, 'bytes': 111952, 'sha256': 'd01242b525a8338b9728e63164e4fae6049449a7edd8ef52dc157ec36cb54b91', 'git_blob': 'f6c2fc30a08195d43d4a730360aa97453301ab6c'}], 'member_count': 44, 'expanded_member_bytes': 16917132, 'manifest': {'member': 'FILE_MANIFEST.json', 'shape': 'files_list', 'schema': 'p29_nonunit_full_evidence_manifest_v1', 'bytes': 8383, 'sha256': '0780beabbd67410fc72275b3a0bd1c5907ed5822eb90999b3cb33cf58bc095b9'}}, {'id': 'unit128', 'archive': {'bytes': 5933976, 'sha256': '06fb1ee80e841571ead9ce262042b130c76be70c93c4880b40b5d21cb74c0f0f'}, 'parts': [{'index': 0, 'offset': 0, 'bytes': 1350000, 'sha256': '47ad28f02f871a20c14f2f0ee86ac51b1c459c55c01637cdb8cbe6cbb64dd41d', 'git_blob': '32395104de3baead7a464a2aa43a2fc4bfaffce1'}, {'index': 1, 'offset': 1350000, 'bytes': 1350000, 'sha256': 'd37072efea0de5affda8658a6641d5f739577f61663b21534b0880d6ae02df26', 'git_blob': 'bf8d9b2308df6c680371fb738880218ac49e2400'}, {'index': 2, 'offset': 2700000, 'bytes': 1350000, 'sha256': '5552a6820d66e645084702d70e0abe73cdabb3be2ec78bcd76be968eefec4d0d', 'git_blob': '95e48d0a05ba09c21ed396de0b1ef7d362301090'}, {'index': 3, 'offset': 4050000, 'bytes': 1350000, 'sha256': '0d8b105be90f5ee1bd6c219ffe08828ca0a863b07dbf15565d8db71ae4d54455', 'git_blob': 'eebb92bd293f60e5e2f07a8a0baa06bb3f3beb2a'}, {'index': 4, 'offset': 5400000, 'bytes': 533976, 'sha256': 'e4faa0fe1f79b2944441f15b70d42fc4720285269a2eb3fe255c09c357c0d1a1', 'git_blob': '36ec73e4e332f9148bbb680a044c9fbdf8551a7d'}], 'member_count': 128, 'expanded_member_bytes': 105617839, 'manifest': {'member': 'FILE_MANIFEST.json', 'shape': 'files_dictionary', 'schema': 'p29_unit_tail_complete_current_receiver_evidence_v1', 'bytes': 22426, 'sha256': 'f6246295885137041434ed75c773e4e1d578345bdd552c1033caba016fe36ec3'}}], 'documents': {'native14_index': {'bytes': 35907, 'sha256': 'ce7f66e7f392a9574ad8ed4cb03a6dd9451c17699f407ce7eddfc03eb83b6daf', 'git_blob': '65f2cb2a0aafffdca7bfc42d3c46478b2be5936f'}, 'buchstab12_index': {'bytes': 12606, 'sha256': 'a0cc503bcf3666650cfe7fd33573ffbaf9c1aa099ec78dcc58b6e34fbf565be3', 'git_blob': 'b23868ddc9c0dd772b98bb1baa3546c15f2d0c48'}, 'buchstab12_root_review': {'bytes': 2643, 'sha256': 'ecc73705d30291d29e5ab7207477fb775f39521037b7b09556fbba3ec5419949', 'git_blob': '3bad85bf16f74ce52036bdef692a738e10badb56'}, 'fibre_frozen_index': {'bytes': 11341, 'sha256': '25792a0b27c5d9204a4b521e6b92bb690db9aead1890fb655c519bd4f7585554', 'git_blob': '5ef6ca4bd4e2cb969eed630edeb48f5553ab4946'}, 'nonunit44_manifest': {'bytes': 8383, 'sha256': '0780beabbd67410fc72275b3a0bd1c5907ed5822eb90999b3cb33cf58bc095b9', 'git_blob': '00995249f324606b6a33b376df0948abd6694236'}, 'nonunit44_transport': {'bytes': 6412, 'sha256': 'f0b93773417cba1df5c5587ce54ebb32105db90f3b043dee81696c2561ebfd58', 'git_blob': '4a919c8a8fb8c5044c5d2b69cb14bf8e1f395abe'}, 'nonunit002_root_review': {'bytes': 3839, 'sha256': '49b8d37858e3e747067c38accfbbca10458f86f61b1bc273b09578954a5f9296', 'git_blob': 'cdf0f61bd037bca3f295d407db6e5019a12d6e5c'}, 'roughmass_reception': {'bytes': 14657, 'sha256': '343cd864d6d5736e5a6155cf4b87bd5603c0d4d3b5ff2f306c878877ea3a2e91', 'git_blob': '2d1f65599fd058d7db3ed287a9fdf59877cc7b69'}}, 'scope': {'only_bytes_transport': True, 'Lean_or_old_proof_replays': 0, 'native_standard_actual_import_union_qualified': False, 'old54_P2_project_objects_untouched': True, 'new_credit': 0, 'different_candidates_retained_not_declared_equivalent': True}}
BASE = Path(PIN['base'])
MIN_FREE_BYTES = 64 * 1024 * 1024
MAX_CAPTURE_BYTES = 4 * 1024 * 1024
MAX_STDOUT_BYTES = 131072
current_stage = 'before-write-capacity-and-contract'
downloads = {}
events = []
created = False


def identity(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest(),
            'git_blob': hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()}


def stamp(s):
    return [s.st_dev, s.st_ino, s.st_mode, s.st_nlink, s.st_size, s.st_mtime_ns, s.st_ctime_ns]


def encode(value):
    return (json.dumps(value, sort_keys=True, indent=2) + '\n').encode('ascii')


def write_new(relative, data):
    path = BASE / relative
    assert path.is_relative_to(BASE) and '..' not in path.parts
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('xb') as stream:
        stream.write(data)
        stream.flush()
    before = stamp(path.stat())
    with path.open('rb') as stream:
        assert stamp(os.fstat(stream.fileno())) == before
        actual = stream.read(len(data) + 1)
        assert stamp(os.fstat(stream.fileno())) == before
    assert actual == data and stamp(path.stat()) == before
    return {'path': str(path), **identity(data), 'stat': before}


def stage(name):
    global current_stage
    current_stage = name
    event = {'stage': name, 'utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    events.append(event)
    if created:
        with (BASE / 'EVENTS.jsonl').open('ab') as stream:
            stream.write((json.dumps(event, sort_keys=True) + '\n').encode('ascii'))


def fetch_blob(pin):
    blob = pin['git_blob']
    assert len(blob) == 40 and all(c in '0123456789abcdef' for c in blob)
    assert isinstance(pin['bytes'], int) and 0 < pin['bytes'] <= 2 * 1024 * 1024
    assert blob not in downloads, 'A Git blob must be fetched only once by this receiver.'
    url = 'https://api.github.com/repos/UyNewNas/goldbach-formalization/git/blobs/' + blob
    bound = 3 * ((4 * (pin['bytes'] + 2)) // 3) + 65536
    with urllib.request.urlopen(url, timeout=45) as response:
        raw = response.read(bound + 1)
    assert len(raw) <= bound
    value = json.loads(raw)
    assert value['encoding'] == 'base64' and value['sha'] == blob and value['size'] == pin['bytes']
    data = base64.b64decode(''.join(value['content'].split()), validate=True)
    actual = identity(data)
    assert actual == {k: pin[k] for k in ('bytes', 'sha256', 'git_blob')}
    downloads[blob] = {'url': url, **actual, 'fetch_count': 1}
    return data


def observe_candidate(path, expected):
    result = {'path': path, 'selected_for_reuse': False}
    try:
        logical = os.lstat(path)
    except FileNotFoundError:
        return {**result, 'classification': 'NO_ENTRY_AT_THIS_EXACT_CANDIDATE'}
    except OSError as exc:
        return {**result, 'classification': 'STAT_ERROR', 'errno': exc.errno, 'message': str(exc)}
    result['logical_lstat'] = stamp(logical)
    try:
        target = os.stat(path)
    except OSError as exc:
        return {**result, 'classification': 'TARGET_STAT_ERROR', 'errno': exc.errno, 'message': str(exc)}
    result['target_stat'] = stamp(target)
    result['observed_bytes'] = target.st_size
    if not stat.S_ISREG(target.st_mode):
        return {**result, 'classification': 'NONREGULAR_TARGET_NOT_REUSED'}
    if target.st_size != expected['bytes']:
        return {**result, 'classification': 'DIFFERENT_SIZE_NOT_HASHED_OR_MODIFIED', 'sha256': None}
    try:
        with open(path, 'rb') as stream:
            assert stamp(os.fstat(stream.fileno())) == result['target_stat']
            data = stream.read(expected['bytes'] + 1)
            assert stamp(os.fstat(stream.fileno())) == result['target_stat']
        assert stamp(os.lstat(path)) == result['logical_lstat']
        assert stamp(os.stat(path)) == result['target_stat']
        assert len(data) == expected['bytes']
        result['sha256'] = hashlib.sha256(data).hexdigest()
        result['classification'] = ('SAME_PIN_STABLE_CANDIDATE' if result['sha256'] == expected['sha256']
                                    else 'DIFFERENT_SHA256_NOT_MODIFIED')
    except (OSError, AssertionError) as exc:
        result['classification'] = 'READ_OR_STABILITY_ERROR_NOT_REUSED'
        result['message'] = str(exc)
    return result


def receive_archive(group, needed):
    archive_path = BASE / 'archives' / (group['id'] + '.tar.xz')
    archive_path.parent.mkdir(parents=True, exist_ok=True)
    full_hash = hashlib.sha256()
    offset = 0
    original_parts = []
    with archive_path.open('xb') as stream:
        for index, part in enumerate(group['parts']):
            assert part['index'] == index and part['offset'] == offset
            data = fetch_blob(part)
            stream.write(data)
            full_hash.update(data)
            offset += len(data)
            original_parts.append({k: part[k] for k in ('index', 'offset', 'bytes', 'sha256', 'git_blob')})
        stream.flush()
    assert offset == group['archive']['bytes'] and full_hash.hexdigest() == group['archive']['sha256']
    before = stamp(archive_path.stat())
    assert before[4] == offset
    wanted = needed | {group['manifest']['member']}
    found = {}
    seen = {}
    total_declared = 0
    with tarfile.open(archive_path, mode='r|xz') as archive:
        for member in archive:
            pure = PurePosixPath(member.name)
            assert member.isfile() and not pure.is_absolute() and '..' not in pure.parts
            assert str(pure) == member.name and member.name not in seen
            assert member.size >= 0
            seen[member.name] = member.size
            total_declared += member.size
            assert total_declared <= group['expanded_member_bytes']
            if member.name not in wanted:
                continue
            assert member.size <= MAX_CAPTURE_BYTES
            source = archive.extractfile(member)
            assert source is not None
            data = source.read(member.size + 1)
            assert len(data) == member.size
            found[member.name] = data
    assert stamp(archive_path.stat()) == before
    assert len(seen) == group['member_count'] and total_declared == group['expanded_member_bytes']
    assert set(found) == wanted
    manifest_bytes = found[group['manifest']['member']]
    assert len(manifest_bytes) == group['manifest']['bytes']
    assert hashlib.sha256(manifest_bytes).hexdigest() == group['manifest']['sha256']
    manifest = json.loads(manifest_bytes)
    if group['manifest']['shape'] == 'direct_dictionary':
        table = manifest
    elif group['manifest']['shape'] == 'files_dictionary':
        assert manifest['schema'] == group['manifest']['schema']
        table = manifest['files']
    else:
        assert group['manifest']['shape'] == 'files_list' and manifest['schema'] == group['manifest']['schema']
        table = {entry['path']: {k: entry[k] for k in ('bytes', 'sha256')} for entry in manifest['files']}
        assert len(table) == len(manifest['files'])
    assert set(table) == set(seen) - {group['manifest']['member']}
    assert all(seen[name] == entry['bytes'] for name, entry in table.items())
    for name in needed:
        assert len(found[name]) == table[name]['bytes']
        assert hashlib.sha256(found[name]).hexdigest() == table[name]['sha256']
    manifest_record = write_new('provenance/' + group['id'] + '/FILE_MANIFEST.json', manifest_bytes)
    return found, {'group': group['id'], 'path': str(archive_path), 'bytes': offset,
        'sha256': full_hash.hexdigest(), 'parts': original_parts, 'archive_stat': before,
        'archive_fetched_once': True, 'manifest': manifest_record,
        'member_count': len(seen), 'captured_members': sorted(wanted),
        'other_member_payloads_materialized_or_audited': False}


try:
    assert isinstance(SOURCE_TEXT, str)
    assert not BASE.exists() and not BASE.is_symlink(), 'Do not rerun an existing receiver; preserve and inspect its receipt.'
    rows = PIN['objects']
    assert len(rows) == len({row['module'] for row in rows}) == 18
    assert sum(row['bytes'] for row in rows) == 9355560
    assert sum(row['bytes'] for row in rows if row['kind'] == 'native') == 8466440
    assert sum(row['bytes'] for row in rows if row['kind'] == 'foreign_project') == 889120
    for row in rows:
        relative = row['module'].replace('.', '/') + '.olean'
        assert row['destination_relative'] == 'lib/lean/' + relative
        assert row['P2_candidates'] == [root + '/' + relative for root in PIN['candidate_roots']]
        assert 0 < row['bytes'] <= 2 * 1024 * 1024
    free_before = shutil.disk_usage('/workspace').free
    assert free_before >= MIN_FREE_BYTES, 'Insufficient disk space before any receiver write.'
    BASE.mkdir(mode=0o700, parents=False, exist_ok=False)
    created = True
    receiver_record = write_new('receiver.py', SOURCE_TEXT.encode())
    contract_record = write_new('PIN_CONTRACT.json', encode(PIN))
    stage('fixed-small-source-authorities')
    documents = {}
    authority_records = {}
    for key, entry in PIN['documents'].items():
        raw = fetch_blob(entry)
        documents[key] = json.loads(raw)
        authority_records[key] = write_new('provenance/authorities/' + key + '.json', raw)
    native_index = {row['module']: row for row in documents['native14_index']['rows']}
    for row in rows:
        if row['kind'] == 'native':
            old = native_index[row['module']]['P1_exact_required_object']
            assert row['bytes'] == old['bytes'] and row['sha256'] == old['sha256']
            assert row['original_object_path'] == old['path']
    buchstab = documents['buchstab12_index']
    assert buchstab['archive']['bytes'] == PIN['archives'][0]['archive']['bytes']
    assert buchstab['archive']['sha256'] == PIN['archives'][0]['archive']['sha256']
    assert buchstab['parts'] == PIN['archives'][0]['parts']
    assert {x['module']: (x['bytes'], x['sha256'], x['member']) for x in buchstab['object_rows']} == {
        row['module']: (row['bytes'], row['sha256'], row['object_member']) for row in rows if row['provider'] == 'buchstab12'}
    unit_index = documents['fibre_frozen_index']
    unit_group = next(group for group in PIN['archives'] if group['id'] == 'unit128')
    unit_transport = unit_index['original_archive']['archive']['transport_xz']
    assert unit_group['archive'] == {k: unit_transport[k] for k in ('bytes', 'sha256')}
    assert unit_group['member_count'] == unit_index['manifest']['members']
    assert unit_group['manifest']['bytes'] == unit_index['manifest']['bytes']
    assert unit_group['manifest']['sha256'] == unit_index['manifest']['sha256']
    for part, original in zip(unit_group['parts'], unit_index['original_archive']['parts']):
        assert all(part[k] == original[k] for k in ('index', 'bytes', 'sha256', 'git_blob'))
        assert part['offset'] == original['byte_offset']
    assert len(unit_group['parts']) == len(unit_index['original_archive']['parts'])
    native_group = next(group for group in PIN['archives'] if group['id'] == 'nonunit44')
    native_transport = documents['nonunit44_transport']
    assert native_group['archive'] == {'bytes': native_transport['archive']['archive_bytes'],
        'sha256': native_transport['archive']['archive_sha256']}
    assert native_group['manifest']['sha256'] == native_transport['archive']['file_manifest_sha256']
    assert native_group['member_count'] == native_transport['archive']['tar_members']
    assert len(native_group['parts']) == len(native_transport['parts'])
    for part, original in zip(native_group['parts'], native_transport['parts']):
        assert all(part[k] == original[k] for k in ('bytes', 'sha256', 'git_blob'))
    unit = {row['module']: row for row in unit_index['rows']}
    for row in rows:
        if row['provider'] == 'unit128':
            old = unit[row['module']]
            assert old['object'] == {k: row[k] for k in ('bytes', 'sha256')}
            assert old['object_member'] == row['object_member']
            assert old['source'] == {k: row['source'][k] for k in ('bytes', 'sha256')}
            assert old['source_member'] == row['source']['member']
    old_native_table = {x['path']: x for x in documents['nonunit44_manifest']['files']}
    for row in rows:
        if row['provider'] == 'nonunit44':
            for item, member in ((row, row['object_member']), (row['source'], row['source']['member'])):
                assert old_native_table[member]['bytes'] == item['bytes']
                assert old_native_table[member]['sha256'] == item['sha256']
    nonunit = next(row for row in rows if row['module'] == 'ImbalancedChen.P2FiniteMarkedGamma5NonunitQuotient')
    old = documents['nonunit002_root_review']
    assert old['object_bytes'] == nonunit['bytes'] and old['object_sha256'] == nonunit['sha256']
    assert old['source_blob'] == nonunit['source']['git_blob'] and old['source_sha256'] == nonunit['source']['sha256']
    rough = next(row for row in rows if row['module'] == 'ImbalancedChen.P2FiniteMarkedGamma5RadialRoughMass')
    for key, item in (('object', rough), ('source', rough['source'])):
        original = documents['roughmass_reception'][key]
        assert all(original[k] == item[k] for k in ('bytes', 'sha256', 'git_blob'))
    stage('exact-authorized-candidate-observations')
    observations = {}
    selected = {}
    for row in rows:
        candidates = [observe_candidate(path, row) for path in row['P2_candidates']]
        observations[row['module']] = candidates
        match = next((c for c in candidates if c['classification'] == 'SAME_PIN_STABLE_CANDIDATE'), None)
        if match is not None:
            match['selected_for_reuse'] = True
            selected[row['module']] = {'selected_path': match['path'], 'selection': 'REUSE_EXISTING_SAME_PIN',
                'bytes': row['bytes'], 'sha256': row['sha256'], 'original_candidate': dict(match)}
    archive_receipts = []
    source_records = {}
    for group in PIN['archives']:
        stage('single-archive-' + group['id'])
        group_rows = [row for row in rows if row['provider'] == group['id']]
        needed = {row['object_member'] for row in group_rows if row['module'] not in selected}
        needed |= {row['source']['member'] for row in group_rows if row['source'] is not None}
        payloads, archive_receipt = receive_archive(group, needed)
        archive_receipts.append(archive_receipt)
        for row in group_rows:
            if row['module'] not in selected:
                data = payloads.pop(row['object_member'])
                assert len(data) == row['bytes'] and hashlib.sha256(data).hexdigest() == row['sha256']
                record = write_new(row['destination_relative'], data)
                selected[row['module']] = {'selected_path': record['path'], 'selection': 'NEW_EXCLUSIVE_COPY_OF_SPECIFIED_PIN',
                    'bytes': row['bytes'], 'sha256': row['sha256'], 'new_file': record}
            if row['source'] is not None:
                data = payloads.pop(row['source']['member'])
                assert len(data) == row['source']['bytes'] and hashlib.sha256(data).hexdigest() == row['source']['sha256']
                source_records[row['module']] = write_new('sources/' + row['module'].replace('.', '/') + '.lean', data)
        assert set(payloads) == {group['manifest']['member']}
    stage('existing-standalone-Git-source-and-object-bytes')
    for row in rows:
        if row['provider'] != 'standalone_git':
            continue
        if row['module'] not in selected:
            data = fetch_blob(row)
            record = write_new(row['destination_relative'], data)
            selected[row['module']] = {'selected_path': record['path'], 'selection': 'NEW_EXCLUSIVE_COPY_OF_EXISTING_Git_BLOB',
                'bytes': row['bytes'], 'sha256': row['sha256'], 'new_file': record}
        data = fetch_blob(row['source'])
        source_records[row['module']] = write_new('sources/' + row['module'].replace('.', '/') + '.lean', data)
    stage('final-selected-object-stability-and-byte-receipt')
    assert len(selected) == 18 and len(source_records) == 6
    for row in rows:
        choice = selected[row['module']]
        if choice['selection'] == 'REUSE_EXISTING_SAME_PIN':
            old = choice['original_candidate']
            assert stamp(os.lstat(choice['selected_path'])) == old['logical_lstat']
            assert stamp(os.stat(choice['selected_path'])) == old['target_stat']
            choice['final_stat'] = stamp(os.stat(choice['selected_path']))
        else:
            assert stamp(os.stat(choice['selected_path'])) == choice['new_file']['stat']
            choice['final_stat'] = choice['new_file']['stat']
        choice['source_received'] = source_records.get(row['module'])
        choice['provenance'] = row['provenance']
        choice['member_provenance'] = {'provider': row['provider'], 'member': row.get('object_member'),
            'existing_git_blob': row.get('git_blob'), 'source_member_or_Git': row['source']}
    result = {'schema': 'p29_omitted_P2_exact18_object_byte_reception_v1',
        'status': 'PASS_EXACT_BYTES_ONLY_NOT_MATHEMATICAL_OR_ACTUAL_IMPORT_QUALIFICATION',
        'root': str(BASE), 'receiver': receiver_record, 'pin_contract': contract_record,
        'selected_objects': selected, 'authorized_candidate_observations': observations,
        'archives': archive_receipts, 'authorities': authority_records, 'downloads': downloads,
        'counts': {'objects': 18, 'native_objects': 14, 'foreign_project_objects': 4,
            'object_bytes': 9355560, 'native_bytes': 8466440, 'foreign_project_bytes': 889120,
            'received_source_files': 6, 'native12_formal_sources_received': 0,
            'reused_existing_objects': sum(v['selection'] == 'REUSE_EXISTING_SAME_PIN' for v in selected.values()),
            'authorized_candidates_checked': sum(len(v) for v in observations.values()),
            'archive_packages_received_once': len(archive_receipts)},
        'capacity': {'free_bytes_before': free_before, 'minimum_free_bytes': MIN_FREE_BYTES,
            'requested_task_memory_mb': 512, 'requested_cpu_threads': 1,
            'maximum_captured_member_bytes': MAX_CAPTURE_BYTES, 'actual_Git_raw_bytes_received': sum(x['bytes'] for x in downloads.values())},
        'scope': {'old_P2_project54_modified': False, 'different_candidate_overwritten': False,
            'unlisted_paths_scanned': False, 'global_absence_claim': False, 'Lean_invocations': 0,
            'normal_kernel_owned_replays': 0, 'new_formal_credit': 0,
            'actual_native_standard_import_union_qualified': False,
            'next_stage_owner': 'atlas: explicit search paths and a single actual module/facet binding'},
        'events': events, 'completed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    raw = encode(result)
    assert len(raw) < MAX_STDOUT_BYTES
    write_new('BYTE_RECEPTION_RECEIPT.json', raw)
    print('P29_OMITTED_P2_BYTE_RECEPTION ' + json.dumps(result, sort_keys=True, separators=(',', ':')), flush=True)
except Exception as exc:
    failure = {'schema': 'p29_omitted_P2_byte_receiver_first_failure_v1', 'stage': current_stage,
        'exception_type': type(exc).__name__, 'message': str(exc), 'root': str(BASE),
        'new_root_created': created, 'completed_downloads': downloads, 'events': events,
        'Lean_invocations': 0, 'new_formal_credit': 0}
    if created and not (BASE / 'FIRST_FAILURE.json').exists():
        write_new('FIRST_FAILURE.json', encode(failure))
    print('P29_OMITTED_P2_BYTE_RECEPTION_FAILURE ' + json.dumps(failure, sort_keys=True), flush=True)
    raise
