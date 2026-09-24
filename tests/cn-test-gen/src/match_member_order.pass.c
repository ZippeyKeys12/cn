// A constructor whose declared member order is not alphabetical, destructured
// by a non-recursive function that a precondition applies. Bennet inlines the
// function's WellTyped body, whose pattern lists members sorted by name
// (`{ Tail: _, Value: v }` for a declaration `{ Value, Tail }`), so the pattern
// compiler must bind members by name: bound positionally, `headValue` reads
// the tail and the generator admits inputs the target's own precondition
// check rejects.

struct node {
    int value;
    struct node *next;
};

/*@
datatype ValueList {
    VL_Nil {},
    VL_Cons { i32 Value, datatype ValueList Tail }
}

function (boolean) nonEmpty(datatype ValueList xs) {
    match xs {
        VL_Nil {} => { false }
        VL_Cons { Value: _, Tail: _ } => { true }
    }
}

function (i32) headValue(datatype ValueList xs) {
    match xs {
        VL_Nil {} => { 0i32 }
        VL_Cons { Value: v, Tail: _ } => { v }
    }
}

predicate [rec] (datatype ValueList) ValueList(pointer p) {
    if (is_null(p)) {
        return VL_Nil {};
    } else {
        take H = RW<struct node>(p);
        take Rest = ValueList(H.next);
        return VL_Cons { Value: H.value, Tail: Rest };
    }
}
@*/

int head_at_most(struct node *p, int bound)
/*@ requires take L = ValueList(p);
             !nonEmpty(L) || headValue(L) <= bound;
    ensures  take L_post = ValueList(p);
             L_post == L;
             return == (nonEmpty(L) ? headValue(L) : 0i32);
@*/
{
    if (p == (struct node *)0) {
        return 0;
    }
    return p->value;
}
