Basics.vo Basics.glob Basics.v.beautified: Basics.v
Basics.vio: Basics.v
Induction.vo Induction.glob Induction.v.beautified: Induction.v Basics.vo
Induction.vio: Induction.v Basics.vio
Lists.vo Lists.glob Lists.v.beautified: Lists.v Induction.vo
Lists.vio: Lists.v Induction.vio
PolyTest.vo PolyTest.glob PolyTest.v.beautified: PolyTest.v Poly.vo
PolyTest.vio: PolyTest.v Poly.vio
Poly.vo Poly.glob Poly.v.beautified: Poly.v Lists.vo
Poly.vio: Poly.v Lists.vio
TacticsTest.vo TacticsTest.glob TacticsTest.v.beautified: TacticsTest.v Tactics.vo
TacticsTest.vio: TacticsTest.v Tactics.vio
Tactics.vo Tactics.glob Tactics.v.beautified: Tactics.v Poly.vo
Tactics.vio: Tactics.v Poly.vio
