module Disjoint_set = struct
  module type Elt = sig
    type t

    val equal : t -> t -> bool

    val compare : t -> t -> int

    val hash : t -> int
  end

  module Make (Elt : Elt) = struct
    type elt = Elt.t

    type t = { data : (elt, elt) Hashtbl.t; disjointed_number : int ref }

    let empty = { data = Hashtbl.create 100; disjointed_number = ref 0 }

    let make_set t elt =
      if not (Hashtbl.mem t.data elt) then (
        Hashtbl.add t.data elt elt;
        incr t.disjointed_number )


    let rec find t elt =
      let parent = Hashtbl.find t.data elt in
      if parent <> elt then
        (* path compression *)
        Hashtbl.replace t.data elt (find t parent);
      Hashtbl.find t.data elt


    let union t x y =
      let x_parent = find t x in
      let y_parent = find t y in
      if x_parent <> y_parent then (
        decr t.disjointed_number;
        Hashtbl.replace t.data x_parent y_parent )


    let same_set t x y = find t x = find t y

    let disjointed_number t = !(t.disjointed_number)

    module EltSet = Set.Make (Elt)
    module SetOfDisjointSet = Set.Make (EltSet)

    (** Yield set of disjoint sets *)
    let to_set t =
      let tbl_set = Hashtbl.create 100 in
      Hashtbl.iter
        (fun elt parent ->
          (* find my set *)
          let set =
            match Hashtbl.find_opt tbl_set parent with
            | Some set -> set
            | None -> EltSet.empty
          in

          (* add me *)
          let set = EltSet.add elt set in

          (* replace tbl_set *)
          Hashtbl.replace tbl_set parent set)
        t.data;
      Hashtbl.fold
        (fun _ set acc -> SetOfDisjointSet.add set acc)
        tbl_set SetOfDisjointSet.empty
  end
end
