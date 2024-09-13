package sketchral

import util.TreeConstraint

class ConstraintTrier (val constraints: List<TreeConstraint>) {
    // TODO Could try introducing constraints until we equality saturate or something
    /*
    Ask sketch. Is it satisfiable to fill in
    some
    unknowntypet1 = type(label, nochildren)?
    we need to tell sketch that types can have or not have children
    and that int doesn't have children
     */
}