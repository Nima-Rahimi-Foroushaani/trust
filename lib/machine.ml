(**represents the simplest value, supported by our abstract machine.
  In a symbolic machine, of course it would be a symbol.
  In a concrete machine, it can be a simple integer for example*)
module type BASE_VALUE = sig
  type t

  val ( = ) : t -> t -> bool
end

module Ins = struct
  module type S = sig
    type vlu

    type ins
  end

  module Make =
  functor
    (BV : BASE_VALUE)
    ->
    struct
      type base_vlu = BV.t

      type vlu = VluUnit | VluInt of base_vlu

      type ghost_ins =
        | GhImmute of Id.t
        | GhIntro of Id.t
        | GhNow of Id.t
        | GhRealize of Id.t
        | GhUrealize of Id.t

      type ins =
        | InsMutBor of Id.t * Id.t * Id.t
        | InsRaw of Id.t * Id.t
        | InsDrop of Id.t
        | InsSwap of Id.t * Id.t
        | InsMkPtr of Id.t * Id.t
        | InsDeref of Id.t * Id.t
        | InsCopy of Id.t * Id.t
        | InsCnst of Id.t * vlu
        | InsGhost of ghost_ins
    end
end

module Prog = struct
  module type S = sig
    type label = int

    type ins

    type prog = ins list
  end

  module Make =
  functor
    (I : Ins.S)
    ->
    struct
      type label = int

      type ins = I.ins

      type prog = ins list
    end
end
