open util/ordering [State]

sig Object { }
one sig Root extends Object { }

sig State {
    pointers: Object -> set Object - Root,
    collected: set Object,
}

fun live(s: State): set Object {
    Root.*(s.pointers)
}

pred mutate(s, t: State) {
    t.collected = s.collected
    t.pointers != s.pointers
    all a: Object - t.live |
        t.pointers[a] = s.pointers[a]
    all a: t.live |
        t.pointers[a] in s.live
}

pred gc(s, t: State) {
    t.pointers = s.pointers
    t.collected = s.collected + (Object - s.live)
    some t.collected - s.collected
}

fact {
    first.pointers = Root -> (Object - Root)
    no first.collected
    all s: State - last | let t = s.next |
        mutate[s, t] or gc[s, t]
}

assert no_dangling {
    all s: State | no (s.collected & s.live)
}

check no_dangling for 5 Object, 10 State

pred Show {
    #(last.pointers) >= 5
    some last.collected
}

run Show for 5
