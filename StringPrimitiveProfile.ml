(* Native string-primitive baseline and oracle harness.

   The native implementation uses packed positions [16 * byte + tag], whereas
   the ordinary extraction uses logical positions [9 * byte + tag].  Conversion
   is deliberately performed only while checking results, never in a timed or
   allocation region. The frozen handwritten baseline remains independent of
   the selected bindings. Paired timing samples alternate baseline/candidate
   order; both selected and candidate implementations retain oracle checks. *)

module Native = StringBitsBaseline
module Selected = StringBits
module Candidate = NativeStringWorker
module Oracle = Patricia_reference.StringBits

type sample = { seconds : float; words : float; checksum : int }

let packed logical =
  ((logical / 9) lsl 4) lor (logical mod 9)

let logical packed =
  let byte = packed lsr 4 and tag = packed land 15 in
  if tag < 0 || tag > 8 then failwith "invalid packed primitive result";
  (9 * byte) + tag

let option_map f = function None -> None | Some x -> Some (f x)

let consume_bool value = if value then 1 else 0
let consume_option = function None -> 0 | Some value -> value + 1

let median values =
  let ordered = List.sort Stdlib.compare values in
  List.nth ordered (List.length ordered / 2)

let min_max values = (List.hd values, List.hd (List.rev values))

let measure repetitions operation =
  Gc.full_major ();
  let before = Gc.quick_stat () in
  let start = Unix.gettimeofday () in
  let checksum = ref 0 in
  for _ = 1 to repetitions do checksum := !checksum lxor operation () done;
  let elapsed = Unix.gettimeofday () -. start in
  let after = Gc.quick_stat () in
  { seconds = elapsed;
    words = (after.Gc.minor_words +. after.Gc.major_words)
            -. (before.Gc.minor_words +. before.Gc.major_words);
    checksum = !checksum }

let report_samples name repetitions samples =
  let times = List.map (fun x -> x.seconds) samples in
  let words = List.map (fun x -> x.words) samples in
  let lo, hi = min_max (List.sort Stdlib.compare times) in
  Printf.printf "  %-28s median %8.3f ns/op  range %8.3f-%8.3f  words %.0f  checksum %d\n%!"
    name (1e9 *. median times /. float_of_int repetitions)
    (1e9 *. lo /. float_of_int repetitions)
    (1e9 *. hi /. float_of_int repetitions)
    (median words) (List.hd samples).checksum

let report_pair ?(prepare = fun () -> ()) name repetitions current candidate =
  let measured operation = prepare (); measure repetitions operation in
  ignore (measured current);
  ignore (measured candidate);
  let current_samples = ref [] and candidate_samples = ref [] in
  for round = 1 to 7 do
    let baseline () = current_samples := measured current :: !current_samples
    and replacement () = candidate_samples := measured candidate :: !candidate_samples in
    if round mod 2 = 0 then (replacement (); baseline ())
    else (baseline (); replacement ())
  done;
  report_samples ("baseline " ^ name) repetitions !current_samples;
  report_samples ("candidate " ^ name) repetitions !candidate_samples

let independently_equal s = Bytes.to_string (Bytes.of_string s)

let byte_string length seed =
  Stdlib.String.init length
    (fun index -> Char.chr ((seed + (29 * index)) land 255))

let verify_pair left right =
  let limit = 9 * max (Stdlib.String.length left) (Stdlib.String.length right) + 1 in
  for position = 0 to limit do
    if Native.bit_at left (packed position) <> Oracle.bit_at left position then
      failwith "bit_at oracle mismatch";
    if Selected.bit_at left (packed position) <> Candidate.packed_bit_at left (packed position) then
      failwith "selected bit_at mismatch"
  done;
  if option_map logical (Native.first_diff left right)
     <> Oracle.first_diff left right then
    failwith "first_diff oracle mismatch";
  if Candidate.first_diff_indexed left right <> Native.first_diff left right then
    failwith "first_diff candidate mismatch";
  if Selected.first_diff left right <> Native.first_diff left right then
    failwith "selected first_diff mismatch";
  if Candidate.first_diff_indexed_with_identity left right
     <> Native.first_diff left right then
    failwith "first_diff identity candidate mismatch";
  for split = 0 to limit do
    let split = packed split in
    if Native.agrees_before_bounded left right split
       <> Oracle.agrees_before_bounded left right (logical split) then
      failwith "agrees_before_bounded oracle mismatch";
    if Selected.agrees_before_bounded left right split
       <> Native.agrees_before_bounded left right split then
      failwith "selected bounded mismatch";
    if Candidate.bounded_prefix_scan left right (split lsr 4) (split land 15)
       <> Native.agrees_before_bounded left right split then
      failwith "bounded candidate mismatch"
  done

let verify_long_pair left right split =
  (* The proof-aligned extraction structurally decomposes strings.  Checking
     every position of a kilobyte input would therefore benchmark the oracle,
     not validate this harness.  The exhaustive position/tag check above is
     retained for short binary cases; long cases check the operations used by
     the timed workloads once each. *)
  if option_map logical (Native.first_diff left right)
     <> Oracle.first_diff left right then
    failwith "long first_diff oracle mismatch";
  if Candidate.first_diff_indexed left right <> Native.first_diff left right then
    failwith "long first_diff candidate mismatch";
  if Candidate.first_diff_indexed_with_identity left right
     <> Native.first_diff left right then
    failwith "long first_diff identity candidate mismatch";
  if Native.agrees_before_bounded left right split
     <> Oracle.agrees_before_bounded left right (logical split) then
    failwith "long agrees_before_bounded oracle mismatch";
  if Candidate.bounded_prefix_scan left right (split lsr 4) (split land 15)
     <> Native.agrees_before_bounded left right split then
      failwith "long bounded candidate mismatch"

let verify_exhaustive_one_byte_pairs () =
  (* This is deliberately a direct candidate/current differential check: the
     proof-aligned structural extraction is already exercised on the compact
     oracle matrix above, whereas invoking it at every split of 65,536 pairs
     would measure repeated substring construction rather than the candidate. *)
  for left_code = 0 to 255 do
    let left = Stdlib.String.make 1 (Char.chr left_code) in
    for right_code = 0 to 255 do
      let right = Stdlib.String.make 1 (Char.chr right_code) in
      if Candidate.first_diff_indexed_with_identity left right
         <> Native.first_diff left right then
        failwith "exhaustive one-byte first_diff candidate mismatch";
      for tag = 0 to 8 do
        let split = tag in
        if Candidate.bounded_prefix_scan left right 0 tag
           <> Native.agrees_before_bounded left right split then
          failwith "exhaustive one-byte bounded candidate mismatch"
      done
    done
  done

let () =
  let prefix = byte_string 1024 17 in
  let differing = Bytes.of_string prefix in
  Bytes.set differing 1023 '\255';
  let differing = Bytes.to_string differing in
  let proper_prefix = Stdlib.String.sub prefix 0 1023 in
  let binary = "\000\255\128\001" in
  List.iter (fun value -> verify_pair value value)
    [""; "\000"; binary; "a"; "a\000b"; "a\255b"];
  verify_pair binary "\000\255\129\001";
  let long_split = packed (9 * 1023 + 8) in
  verify_long_pair prefix differing long_split;
  verify_long_pair prefix proper_prefix long_split;
  verify_long_pair prefix (independently_equal prefix) long_split;
  verify_exhaustive_one_byte_pairs ();
  Printf.printf "Native string primitive baseline (7 interleaved samples; inputs pre-created)\n%!";
  let positions = Array.init (9 * Stdlib.String.length prefix + 1) packed in
  let index = ref 0 in
  let bit_call worker () =
    let result = worker prefix positions.(!index mod Array.length positions) in
    incr index; consume_bool result in
  report_pair ~prepare:(fun () -> index := 0) "bit_at" 200_000
    (bit_call Native.bit_at) (bit_call Candidate.packed_bit_at);
  let difference_case name repetitions left right =
    report_pair name repetitions
      (fun () -> consume_option (Native.first_diff left right))
      (fun () -> consume_option (Candidate.first_diff_indexed_with_identity left right)) in
  difference_case "same object" 200_000 prefix prefix;
  let equal_copy = independently_equal prefix in
  difference_case "equal copies" 20_000 prefix equal_copy;
  difference_case "late difference" 20_000 prefix differing;
  difference_case "empty" 200_000 "" "";
  difference_case "proper prefix" 20_000 prefix proper_prefix;
  difference_case "early difference" 200_000 "\000abcd" "\255abcd";
  List.iter (fun length ->
    let left = byte_string length 17 in
    let right = independently_equal left in
    verify_long_pair left right (packed (9 * length));
    difference_case (Printf.sprintf "equal length %d" length) 20_000 left right)
    [1; 8; 64; 256; 4096];
  let split = long_split in
  let bounded_case name repetitions left right split =
    report_pair name repetitions
      (fun () -> consume_bool (Native.agrees_before_bounded left right split))
      (fun () -> consume_bool (Candidate.bounded_prefix_packed left right split)) in
  bounded_case "bounded late" 20_000 prefix differing split;
  bounded_case "bounded prefix" 20_000 prefix proper_prefix split;
  bounded_case "bounded empty" 200_000 "" "" 0;
  bounded_case "bounded early" 200_000 "\000a" "\255a" 8;
  for tag = 0 to 8 do
    bounded_case (Printf.sprintf "bounded tag %d" tag) 200_000 binary binary tag
  done;
  Printf.printf "String primitive profile: oracle checks passed\n%!"
