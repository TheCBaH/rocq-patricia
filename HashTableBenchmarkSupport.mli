(** Shared measurement support for the HAMT performance harnesses.

    The harnesses prepare inputs and semantic expectations before handing a
    task to this module.  Each task returns an observable checksum so that the
    timed computation remains live without including its oracle check. *)

type config = {
  repetitions : int;
  warmups : int;
  result_file : string;
}

type task = {
  implementation : string;
  operation : string;
  run : int -> int;
}

val config : unit -> config

(** [start ~workload ~size ~seed] records toolchain and host metadata. *)
val start : workload:string -> size:int -> seed:int -> unit

(** [measure tasks] warms every task, then measures each repetition while
    rotating the implementation order.  The integer argument selects a
    separately prepared input; [-1] is reserved for warmup input. *)
val measure : task list -> unit

(** Measure post-GC live heap while the constructed value remains reachable.
    This is deliberately separate from the allocation and timing samples. *)
val live_heap : implementation:string -> policy:string -> (unit -> 'a) -> 'a

val finish : unit -> unit
