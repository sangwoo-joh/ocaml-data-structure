(* Stole some idea from OCaml Stdlib and Janestreet Base *)
module Tree = struct
  type 'a t =
    | Empty
    | Leaf of 'a  (** same as Node (Empty, x, Empty, 1, 1) *)
    | Node of 'a t * 'a * 'a t * int
        (** left tree, value, right tree, height *)

  let height = function
    | Empty -> 0
    | Leaf _ -> 1
    | Node (_, _, _, h) -> h


  let is_empty = function
    | Empty -> true
    | Leaf _ | Node _ -> false


  (** l and r must be balanced, i.e., | l.height - r.height | <= 2 *)
  let create l v r =
    let hl = height l in
    let hr = height r in
    let h = if hl >= hr then hl + 1 else hr + 1 in
    if h = 1 then Leaf v else Node (l, v, r, h)


  (** Same as create, but performs one step of rebalancing if necessary.
 Assumes l and r are balanaced and | l.height - r.height | <= 3.
*)
  let bal l v r =
    let hl = height l in
    let hr = height r in
    if hl > hr + 2 then
      match l with
      | Empty (* h(l)=0 *) | Leaf _ (* h(l)=1 *) -> assert false
      | Node (ll, lv, lr, _) -> (
          if height ll >= height lr then create ll lv (create lr v r)
          else
            match lr with
            | Empty -> assert false
            | Leaf lrv ->
                assert (is_empty ll);
                create (create ll lv Empty) lrv (create Empty v r)
            | Node (lrl, lrv, lrr, _) ->
                create (create ll lv lrl) lrv (create lrr v r) )
    else if hr > hl + 2 then
      match r with
      | Empty -> assert false
      | Leaf rv -> create (create l v Empty) rv Empty
      | Node (rl, rv, rr, _) -> (
          if height rr >= height rl then create (create l v rl) rv rr
          else
            match rl with
            | Empty -> assert false
            | Leaf rlv ->
                assert (is_empty rr);
                create (create l v Empty) rlv (create Empty rv rr)
            | Node (rll, rlv, rlr, _) ->
                create (create l v rll) rlv (create rlr rv rr) )
    else
      (* same as create *)
      let h = if hl >= hr then hl + 1 else hr + 1 in
      if h = 1 then Leaf v else Node (l, v, r, h)


  exception Same

  let add t x ~compare_elt =
    let rec add = function
      | Empty -> Leaf x
      | Leaf v ->
          let c = compare_elt x v in
          if c = 0 then raise Same
          else if c < 0 then bal (Leaf x) v Empty
          else bal Empty v (Leaf x)
      | Node (l, v, r, _) ->
          let c = compare_elt x v in
          if c = 0 then raise Same
          else if c < 0 then bal (add l) v r
          else bal l v (add r)
    in
    try add t with Same -> t


  (** Same as create/bal, but no assumptions are made on the relative heights of l/r *)
  let rec join l v r ~compare_elt =
    match (l, r) with
    | Empty, _ -> add r v ~compare_elt
    | _, Empty -> add l v ~compare_elt
    | Leaf lv, _ -> add (add r v ~compare_elt) lv ~compare_elt
    | _, Leaf rv -> add (add l v ~compare_elt) rv ~compare_elt
    | Node (ll, lv, lr, lh), Node (rl, rv, rr, rh) ->
        if lh > rh + 2 then bal ll lv (join lr v r ~compare_elt)
        else if rh > lh + 2 then bal (join l v rl ~compare_elt) rv rr
        else create l v r


  let rec min_elt = function
    | Empty -> None
    | Leaf v | Node (Empty, v, _, _) -> Some v
    | Node (l, _, _, _) -> min_elt l


  let min_elt_exn t =
    match min_elt t with
    | None -> invalid_arg "Tree.min_elt_exn"
    | Some v -> v


  let rec max_elt = function
    | Empty -> None
    | Leaf v | Node (_, v, Empty, _) -> Some v
    | Node (_, _, r, _) -> max_elt r


  let rec remove_min_elt = function
    | Empty -> invalid_arg "Tree.remove_min_elt"
    | Leaf _ -> Empty
    | Node (Empty, _, r, _) -> r
    | Node (l, v, r, _) -> bal (remove_min_elt l) v r


  let concat t1 t2 ~compare_elt =
    match (t1, t2) with
    | Empty, t | t, Empty -> t
    | _, _ -> join t1 (min_elt_exn t2) (remove_min_elt t2) ~compare_elt


  let merge t1 t2 =
    match (t1, t2) with
    | Empty, t | t, Empty -> t
    | _, _ -> bal t1 (min_elt_exn t2) (remove_min_elt t2)


  let split t x ~compare_elt =
    let rec split = function
      | Empty -> (Empty, None, Empty)
      | Leaf v ->
          let c = compare_elt x v in
          if c = 0 then (Empty, Some v, Empty)
          else if c < 0 then (Empty, None, Leaf v)
          else (Leaf v, None, Empty)
      | Node (l, v, r, _) ->
          let c = compare_elt x v in
          if c = 0 then (l, Some v, r)
          else if c < 0 then
            let ll, maybe_elt, lr = split l in
            (ll, maybe_elt, join lr v r ~compare_elt)
          else
            let rl, maybe_elt, rr = split r in
            (join l v rl ~compare_elt, maybe_elt, rr)
    in
    split t


  let empty = Empty

  let rec mem t x ~compare_elt =
    match t with
    | Empty -> false
    | Leaf v -> compare_elt x v = 0
    | Node (l, v, r, _) ->
        let c = compare_elt x v in
        c = 0 || mem (if c < 0 then l else r) x ~compare_elt


  let remove t x ~compare_elt =
    let rec remove t =
      match t with
      | Empty -> raise Same
      | Leaf v -> if compare_elt x v = 0 then Empty else raise Same
      | Node (l, v, r, _) ->
          let c = compare_elt x v in
          if c = 0 then merge l r
          else if c < 0 then bal (remove l) v r
          else bal l v (remove r)
    in
    try remove t with Same -> t


  let union s1 s2 ~compare_elt =
    let rec union s1 s2 =
      if s1 == s2 then s1
      else
        match (s1, s2) with
        | Empty, t | t, Empty -> t
        | Leaf v1, _ -> union (Node (Empty, v1, Empty, 1)) s2
        | _, Leaf v2 -> union s1 (Node (Empty, v2, Empty, 1))
        | Node (l1, v1, r1, h1), Node (l2, v2, r2, h2) ->
            if h1 >= h2 then
              if h2 = 1 then add s1 v2 ~compare_elt
              else
                let l2, _, r2 = split s2 v1 ~compare_elt in
                join (union l1 l2) v1 (union r1 r2) ~compare_elt
            else if h1 = 1 then add s2 v1 ~compare_elt
            else
              let l1, _, r1 = split s1 v2 ~compare_elt in
              join (union l1 l2) v2 (union r1 r2) ~compare_elt
    in
    union s1 s2


  let inter s1 s2 ~compare_elt =
    let rec inter s1 s2 =
      if s1 == s2 then s1
      else
        match (s1, s2) with
        | Empty, _ | _, Empty -> Empty
        | (Leaf elt as singleton), other_set | other_set, (Leaf elt as singleton)
          ->
            if mem other_set elt ~compare_elt then singleton else Empty
        | Node (l1, v1, r1, _), t2 -> (
            match split t2 v1 ~compare_elt with
            | l2, None, r2 -> concat (inter l1 l2) (inter r1 r2) ~compare_elt
            | l2, Some v1, r2 ->
                join (inter l1 l2) v1 (inter r1 r2) ~compare_elt )
    in
    inter s1 s2


  let diff s1 s2 ~compare_elt =
    let rec diff s1 s2 =
      if s1 == s2 then Empty
      else
        match (s1, s2) with
        | Empty, _ -> Empty
        | t1, Empty -> t1
        | Leaf v1, t2 -> diff (Node (Empty, v1, Empty, 1)) t2
        | Node (l1, v1, r1, _), t2 -> (
            match split t2 v1 ~compare_elt with
            | l2, None, r2 -> join (diff l1 l2) v1 (diff r1 r2) ~compare_elt
            | l2, Some _, r2 -> concat (diff l1 l2) (diff r1 r2) ~compare_elt )
    in
    diff s1 s2


  let rec find_first_satisfying t ~f =
    match t with
    | Empty -> None
    | Leaf v -> if f v then Some v else None
    | Node (l, v, r, _) ->
        if f v then
          match find_first_satisfying l ~f with
          | None -> Some v
          | Some _ as x -> x
        else find_first_satisfying r ~f


  let rec find_last_satisfying t ~f =
    match t with
    | Empty -> None
    | Leaf v -> if f v then Some v else None
    | Node (l, v, r, _) ->
        if f v then
          match find_first_satisfying r ~f with
          | None -> Some v
          | Some _ as x -> x
        else find_first_satisfying l ~f


  let is_subset s1 ~of_:s2 ~compare_elt =
    let rec is_subset s1 ~of_:s2 =
      match (s1, s2) with
      | Empty, _ -> true
      | _, Empty -> false
      | Leaf v1, t2 -> mem t2 v1 ~compare_elt
      | Node (l1, v1, r1, _), Leaf v2 -> (
          match (l1, r1) with
          | Empty, Empty ->
              (* This case shouldn't occur in practice because we should have constructed a Leaf rather than a Node with two Empty subtrees *)
              compare_elt v1 v2 = 0
          | _, _ -> false )
      | Node (l1, v1, r1, _), (Node (l2, v2, r2, _) as t2) ->
          let c = compare_elt v1 v2 in
          if c = 0 then
            s1 == s2 || (is_subset l1 ~of_:l2 && is_subset r1 ~of_:r2)
          else if c < 0 then
            is_subset (Node (l1, v1, Empty, 0)) ~of_:l2 && is_subset r2 ~of_:t2
          else
            is_subset (Node (Empty, v1, r1, 0)) ~of_:r2 && is_subset l1 ~of_:t2
    in
    is_subset s1 ~of_:s2


  let rec are_disjoint s1 s2 ~compare_elt =
    match (s1, s2) with
    | Empty, _ | _, Empty -> true
    | Leaf v, os | os, Leaf v -> not (mem os v ~compare_elt)
    | Node (l1, v1, r1, _), t2 -> (
        if s1 == s2 then false
        else
          match split t2 v1 ~compare_elt with
          | l2, None, r2 ->
              are_disjoint l1 l2 ~compare_elt && are_disjoint r1 r2 ~compare_elt
          | _, Some _, _ -> false )


  let iter t ~f =
    let rec iter = function
      | Empty -> ()
      | Leaf v -> f v
      | Node (l, v, r, _) ->
          iter l;
          f v;
          iter r
    in
    iter t


  let rec fold t ~init:acc ~f =
    match t with
    | Empty -> acc
    | Leaf v -> f acc v
    | Node (l, v, r, _) -> fold r ~f ~init:(f (fold l ~f ~init:acc) v)


  let rec fold_right t ~init:acc ~f =
    match t with
    | Empty -> acc
    | Leaf v -> f v acc
    | Node (l, v, r, _) ->
        fold_right l ~f ~init:(f v (fold_right r ~f ~init:acc))


  let rec for_all t ~f:p =
    match t with
    | Empty -> true
    | Leaf v -> p v
    | Node (l, v, r, _) -> p v && for_all l ~f:p && for_all r ~f:p


  let rec exists t ~f:p =
    match t with
    | Empty -> false
    | Leaf v -> p v
    | Node (l, v, r, _) -> p v || exists l ~f:p || exists r ~f:p


  let filter s ~f:p ~compare_elt =
    let rec filter acc = function
      | Empty -> acc
      | Leaf v -> if p v then add acc v ~compare_elt else acc
      | Node (l, v, r, _) ->
          filter (filter (if p v then add acc v ~compare_elt else acc) l) r
    in
    filter Empty s


  let map t ~f ~compare_elt =
    fold t ~init:empty ~f:(fun t x -> add t (f x) ~compare_elt)


  let rec find t ~f =
    match t with
    | Empty -> None
    | Leaf v -> if f v then Some v else None
    | Node (l, v, r, _) -> (
        if f v then Some v
        else
          match find l ~f with
          | None -> find r ~f
          | Some _ as x -> x )


  let rec find_map t ~f =
    match t with
    | Empty -> None
    | Leaf v -> f v
    | Node (l, v, r, _) -> (
        match f v with
        | Some _ as x -> x
        | None -> (
            match find_map l ~f with
            | None -> find_map r ~f
            | Some _ as x -> x ) )
end
