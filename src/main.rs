#![feature(nll)]

type Relation = u16;

const ITEMS: [char; 4] = ['a', 'b', 'c', 'd'];

#[inline]
fn is_related_to(r: &Relation, i: usize, j: usize) -> bool {
    r & (1 << (4 * i + j)) != 0
}

#[inline]
fn add_relation(r: &mut Relation, i: usize, j: usize) {
    *r |= 1 << (4 * i + j);
}

fn closure(r: &Relation) -> Relation {
    let mut ret = *r;

    for i in 0..4 {
        add_relation(&mut ret, i, i);
    }

    loop {
        let mut new_ret = ret;

        for i in 0..4 {
            for j in 0..4 {
                for k in 0..4 {
                    if is_related_to(&ret, i, j) && is_related_to(&ret, j, k) {
                        add_relation(&mut new_ret, i, k);
                    }
                }
            }
        }

        if new_ret != ret {
            ret = new_ret;
        } else {
            return new_ret;
        }
    }
}

fn diamond(r: &Relation) -> bool {
    // forall x, y, z. xRy /\ xRz /\ y ≒ z -> exists w. yRw /\ zRw

    for x in 0..4 {
        for y in 0..4 {
            for z in 0..4 {
                if y != z && is_related_to(r, x, y) && is_related_to(r, x, z) {
                    let mut found = false;
                    for w in 0..4 {
                        if is_related_to(r, y, w) && is_related_to(r, z, w) {
                            found = true;
                            break;
                        }
                    }
                    if !found {
                        return false;
                    }
                }
            }
        }
    }

    return true;
}

fn weak_confluence(r: &Relation, r_star: &Relation) -> bool {
    // forall x, y, z. xRy /\ xRz -> exists w. yR*w /\ zR*w

    for x in 0..4 {
        for y in 0..4 {
            for z in 0..4 {
                if is_related_to(r, x, y) && is_related_to(r, x, z) {
                    let mut found = false;
                    for w in 0..4 {
                        if is_related_to(r_star, y, w) && is_related_to(r_star, z, w) {
                            found = true;
                            break;
                        }
                    }
                    if !found {
                        return false;
                    }
                }
            }
        }
    }

    return true;
}

fn print_relation(r: &Relation) {
    for i in 0..4 {
        for j in 0..4 {
            if is_related_to(r, i, j) {
                println!("{} -> {}", ITEMS[i], ITEMS[j]);
            }
        }
    }
}

fn main() {
    for r in 0..=std::u16::MAX {
        let r_star = closure(&r);

        if weak_confluence(&r, &r_star) {
            // R is confluent <-> R* is diamond
            if !diamond(&r_star) {
                println!("-------------------");
                print_relation(&r);
                println!("↓");
                print_relation(&r_star);
                println!("");
            }
        }
    }
}
