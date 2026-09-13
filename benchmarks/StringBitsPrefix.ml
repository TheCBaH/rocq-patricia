module Historical = StringBitsBaseline
module Generated = NativeStringWorker
let bit_at = Historical.bit_at
let first_diff = Historical.first_diff
let agrees_before left right split =
  match first_diff left right with None -> true | Some differing -> split <= differing
let agrees_before_bounded = Generated.bounded_prefix_packed
