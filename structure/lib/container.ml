module Continue_or_stop = struct
  (** used by [f] argument to [fold_until] in order to indicate whether folding should continue or stop early. *)
  type ('a, 'b) t = Continue of 'a | Stop of 'b
end

module type Summable = sig
  type t

  val zero : t

  val ( + ) : t -> t -> t
end

module type Generic = sig
  type 'a t

  type 'a elt

  val length : _ t -> int

  val is_empty : _ t -> bool

  val iter : 'a t -> f:('a elt -> unit) -> unit

  val fold : 'a t -> init:'acc -> f:('acc -> 'a elt -> 'acc) -> 'acc

  val fold_result :
    'a t ->
    init:'acc ->
    f:('acc -> 'a elt -> ('acc, 'e) Result.t) ->
    ('acc, 'e) Result.t

  val fold_until :
    'a t ->
    init:'acc ->
    f:('acc -> 'a elt -> ('acc, 'final) Continue_or_stop.t) ->
    finish:('acc -> 'final) ->
    'final

  val exists : 'a t -> f:('a elt -> bool) -> bool

  val for_all : 'a t -> f:('a elt -> bool) -> bool

  val count : 'a t -> f:('a elt -> bool) -> int

  val sum :
    (module Summable with type t = 'sum) -> 'a t -> f:('a elt -> 'sum) -> 'sum

  val find : 'a t -> f:('a elt -> bool) -> 'a elt option

  val find_map : 'a t -> f:('a elt -> 'b option) -> 'b option

  val to_list : 'a t -> 'a elt list

  val to_array : 'a t -> 'a elt array

  val min_elt : 'a t -> compare:('a elt -> 'a elt -> int) -> 'a elt option

  val max_elt : 'a t -> compare:('a elt -> 'a elt -> int) -> 'a elt option
end

module type Make_gen_arg = sig
  type 'a t

  type 'a elt

  val fold : 'a t -> init:'acc -> f:('acc -> 'a elt -> 'acc) -> 'acc

  val iter :
    [ `Define_using_fold | `Custom of 'a t -> f:('a elt -> unit) -> unit ]
  (** The [iter] argument to [Container.Make] specifies how to implement the
      container's [iter] function.

      [`Define_using_fold] means to define [iter] via: iter t ~f = Container.iter ~fold t ~f

      [`Custom] overrides the default implementation, presumably with something more efficient.
      Several other functions returned by [Container.Make] are defined in terms of [iter],
      so passing in a more efficient [iter] will improve their efficiency as well.
  *)

  val length : [ `Define_using_fold | `Custom of 'a t -> int ]
  (** The [length] argument to [Container.Make] specifies how to implement the
      container's [length] function.

      [`Define_using_fold] means to define [length] via: length t ~f = Container.length ~fold t ~f

      [`Custom] overrides the default implementation, presumably with something more efficient.
      Several other functions returned by [Container.Make] are defined in terms of [length],
      so passing in a more efficient [length] will improve their efficiency as well.
  *)
end

module type Make_arg = Make_gen_arg with type 'a elt := 'a

module With_return = struct
  type 'a return = { return : 'b. 'a -> 'b }

  let with_return (type a) f =
    let module M = struct
      (* Raised to indicate ~return was called.
         Local so that the exception is tied to a particular call of [with_return].
      *)
      exception Return of a
    end in
    let is_alive = ref true in
    let return a =
      if not !is_alive then
        failwith "use of [return] from a [with_return] that already returned";
      Stdlib.raise_notrace (M.Return a)
    in
    try
      let a = f { return } in
      is_alive := false;
      a
    with exn -> (
      is_alive := false;
      match exn with
      | M.Return a -> a
      | _ -> raise exn )
end

let with_return = With_return.with_return

type ('t, 'a, 'acc) fold = 't -> init:'acc -> f:('acc -> 'a -> 'acc) -> 'acc

type ('t, 'a) iter = 't -> f:('a -> unit) -> unit

type 't length = 't -> int

let iter ~fold t ~f = fold t ~init:() ~f:(fun () a -> f a)

let count ~fold t ~f = fold t ~init:0 ~f:(fun n a -> if f a then succ n else n)

let sum (type a) ~fold (module M : Summable with type t = a) t ~f =
  fold t ~init:M.zero ~f:(fun n a -> M.( + ) n (f a))


let fold_result ~fold ~init ~f t =
  with_return (fun { return } ->
      Result.Ok
        (fold t ~init ~f:(fun acc item ->
             match f acc item with
             | Result.Ok x -> x
             | Error _ as e -> return e)))


let fold_until ~fold ~init ~f ~finish t =
  with_return (fun { return } ->
      finish
        (fold t ~init ~f:(fun acc item ->
             match f acc item with
             | Continue_or_stop.Continue x -> x
             | Stop x -> return x)))


let min_elt ~fold t ~compare =
  fold t ~init:None ~f:(fun acc elt ->
      match acc with
      | None -> Some elt
      | Some min -> if compare min elt > 0 then Some elt else acc)


let max_elt ~fold t ~compare =
  fold t ~init:None ~f:(fun acc elt ->
      match acc with
      | None -> Some elt
      | Some max -> if compare max elt < 0 then Some elt else acc)


let length ~fold c = fold c ~init:0 ~f:(fun acc _ -> succ acc)

let is_empty ~iter c =
  with_return (fun r ->
      iter c ~f:(fun _ -> r.return false);
      true)


let exists ~iter c ~f =
  with_return (fun r ->
      iter c ~f:(fun x -> if f x then r.return true);
      false)


let for_all ~iter c ~f =
  with_return (fun r ->
      iter c ~f:(fun x -> if not (f x) then r.return false);
      true)


let find_map ~iter t ~f =
  with_return (fun r ->
      iter t ~f:(fun x ->
          match f x with
          | None -> ()
          | Some _ as res -> r.return res);
      None)


let find ~iter c ~f =
  with_return (fun r ->
      iter c ~f:(fun x -> if f x then r.return (Some x));
      None)


let to_list ~fold c = List.rev (fold c ~init:[] ~f:(fun acc x -> x :: acc))

let to_array ~length ~iter c =
  let array = ref [||] in
  let i = ref 0 in
  iter c ~f:(fun x ->
      if !i = 0 then array := Array.make (length c) x;
      !array.(!i) <- x;
      incr i);
  !array


module Make_gen (T : Make_gen_arg) : sig
  include Generic with type 'a t := 'a T.t with type 'a elt := 'a T.elt
end = struct
  let fold = T.fold

  let iter =
    match T.iter with
    | `Custom iter -> iter
    | `Define_using_fold -> fun t ~f -> iter ~fold t ~f


  let length =
    match T.length with
    | `Custom length -> length
    | `Define_using_fold -> fun t -> length ~fold t


  let is_empty t = is_empty ~iter t

  let sum m t = sum ~fold m t

  let count t ~f = count ~fold t ~f

  let exists t ~f = exists ~iter t ~f

  let for_all t ~f = for_all ~iter t ~f

  let find_map t ~f = find_map ~iter t ~f

  let find t ~f = find ~iter t ~f

  let to_list t = to_list ~fold t

  let to_array t = to_array ~length ~iter t

  let min_elt t ~compare = min_elt ~fold t ~compare

  let max_elt t ~compare = max_elt ~fold t ~compare

  let fold_result t ~init ~f = fold_result t ~fold ~init ~f

  let fold_until t ~init ~f ~finish = fold_until t ~fold ~init ~f ~finish
end

module Make (T : Make_arg) = struct
  include Make_gen (struct
    include T

    type 'a elt = 'a
  end)

  let mem t a ~equal = exists t ~f:(equal a)
end
