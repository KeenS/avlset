#include "share/atspre_staload.hats"

datatype avlt(n: int) =
    Empty(0)
  | {l, m: nat |
    (l + 2 == n && m + 1 == n) ||
    (l + 1 == n && m + 1 == n) ||
    (l + 1 == n && m + 2 == n)
} Node of (avlt(l), int, avlt(m), int(n))




fun height{n: nat}(tree: avlt(n)): int(n) = 
  case+ tree of
  | Empty () => 0
  | Node (_, _, _, n) => n


fun create{
  l, m: nat |
  l + 1 == m ||
  l == m + 1 ||
  l == m
  } (l: avlt(l), v: int, r: avlt(m)): [n: nat | (m > l && n == m + 1) || (l >= m && n == l + 1)] avlt(n) = let
  val hl = height l
  val hr = height r
in
  if hl >= hr
  then Node(l, v, r, hl + 1)
  else Node(l, v, r, hr + 1)
end

fun rotate_right{hl, hr: nat |
  hl == hr + 2
}(l: avlt(hl), v: int, r: avlt(hr)): [n: nat| n == hl || n == hl + 1] avlt(n) = let
  val+ Node(ll, lv, lr, _) = l
  val hll = height ll
  val hlr = height lr
in
  if  hll >= hlr
  then create(ll, lv, create(lr, v, r))
  else let
       val+ Node(lrl, lrv, lrr, _) =  lr
  in
    create(create(ll, lv, lrl), lrv, create(lrr, v, r))
  end
end


fun rotate_left{hl, hr: nat |
  hl + 2 == hr
}(l: avlt(hl), v: int, r: avlt(hr)): [n: nat| n == hr || n == hr + 1] avlt(n) = let
  val+ Node(rl, rv, rr, _) = r
  val hrl = height rl
  val hrr = height rr
in
  if  hrr >= hrl
  then create(create(l, v, rl), rv, rr)
  else let
    val+ Node(rll, rlv, rlr, _) =  rl
  in
    create(create(l, v, rll), rlv, create(rlr, rv, rr))
  end
end


fun bal{hl, hr: nat |
  ~2 <= hl - hr  && hl - hr <= 2
}(l: avlt(hl), v: int, r: avlt(hr)): [n: nat|
 (hl == hr - 2 && n == hr    ) ||
 (hl == hr - 2 && n == hr + 1) ||
 (hl == hr - 1 && n == hr + 1) ||
 (hl == hr     && n == hl + 1) ||
 (hl == hr + 1 && n == hl + 1) ||
 (hl == hr + 2 && n == hl + 1) ||
 (hl == hr + 2 && n == hl    )
] avlt(n) = let
  val hl = height l
  val hr = height r
in
  if hl = hr + 2
  then rotate_right(l, v, r)
  else if hl = hr - 2
  then rotate_left(l, v, r)
  else create(l, v, r)
end



fun cmp(x: int, y: int): int = x - y

fun empty(): avlt(0) = Empty()
fun singleton(x: int): avlt(1) = Node(Empty, x, Empty, 1)


fun insert{m: nat}(x: int, tree: avlt(m)): [n: nat | n == m || n == m + 1]avlt(n) =
  case+ tree of
  | Empty () => singleton(x)
  | t as Node(l, v, r, _) => let
    val c = cmp(x, v)
  in
    if c = 0 then t
    else if c < 0
    then bal(insert(x, l), v, r)
    else bal(l, v, insert(x, r))
  end


fun mem{m: nat}(x: int, tree: avlt(m)): bool =
  case+ tree of
  | Empty () => false
  | Node(l, v, r, _) => let
    val c = cmp(x, v)
  in
    if c = 0
    then true
    else if c < 0
    then mem(x, r)
    else mem(x, l)
  end
  

implement
main0 () =  {
  val tree = empty()
  val tree = insert(1, tree)
  val tree = insert(2, tree)
  val tree = insert(4, tree)
  val b = mem(2, tree)
  val c = mem(3, tree)
  val () = println!(b)
  val () = println!(c)
}
