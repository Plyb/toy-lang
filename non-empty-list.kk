import std/core/unsafe
import std/core/undiv

type non-empty-list<a> {
  NELast(item: a)
  NECons(head: a, tail: non-empty-list<a>)
}

fun non-empty-list/(==)(a: non-empty-list<a>, b: non-empty-list<a>, ?(==): (a, a) -> e bool): e bool {
  match (a, b) {
    (NELast(a_item), NELast(b_item)) -> a_item == b_item
    (NECons(a_head, a_tail), NECons(b_head, b_tail)) ->
      a_head == b_head
      && a_tail.pretend-decreasing == b_tail
    _ -> False
  }
}

fun non-empty-list/show(list: non-empty-list<a>, ?show: a -> string): string {
  match list {
    NELast(item) -> "NELast(" ++ item.show ++ ")"
    NECons(head, tail) -> "NECons(" ++ head.show ++ ", " ++ tail.show ++ ")" 
  }
}

fun assert-non-empty(list: list<a>): exn non-empty-list<a> {
  match list {
    Cons(item, Nil) -> NELast(item)
    Cons(head, tail) -> NECons(head, assert-non-empty(tail))
    Nil -> unsafe-total(fn() throw("bad"))
  }
}

fun first(list: non-empty-list<a>): a {
  match list {
    NELast(item) -> item
    NECons(head, _) -> head
  }
}

fun last(list: non-empty-list<a>): a {
  match list {
    NELast(item) -> item
    NECons(_, tail) -> tail.last
  }
}

fun all_but_last(list: non-empty-list<a>): list<a> {
  match list {
    NELast(_) -> Nil
    NECons(head, tail) -> Cons(head, tail.all_but_last)
  }
}

fun to_list(list: non-empty-list<a>): list<a> {
  match list {
    NELast(item) -> [item]
    NECons(head, tail) -> Cons(head, tail.to_list)
  }
}

fun non-empty-list/map(items: non-empty-list<a>, convert: a -> b): non-empty-list<b> {
  match items {
    NELast(item) -> NELast(convert(item))
    NECons(head, tail) -> NECons(convert(head), tail.map(convert))
  }
}

fun non-empty-list/foldl(items: non-empty-list<a>, starter: b, combine: (acc: b, curr: a) -> b): b {
  items.to_list.foldl(starter, combine)
}
