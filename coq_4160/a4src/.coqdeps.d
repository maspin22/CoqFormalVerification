Basics.vo Basics.glob Basics.v.beautified: Basics.v
Basics.vio: Basics.v
Induction.vo Induction.glob Induction.v.beautified: Induction.v Basics.vo
Induction.vio: Induction.v Basics.vio
Lists.vo Lists.glob Lists.v.beautified: Lists.v Induction.vo
Lists.vio: Lists.v Induction.vio
Logic.vo Logic.glob Logic.v.beautified: Logic.v Tactics.vo
Logic.vio: Logic.v Tactics.vio
LogicTest.vo LogicTest.glob LogicTest.v.beautified: LogicTest.v Logic.vo
LogicTest.vio: LogicTest.v Logic.vio
Poly.vo Poly.glob Poly.v.beautified: Poly.v Lists.vo
Poly.vio: Poly.v Lists.vio
Tactics.vo Tactics.glob Tactics.v.beautified: Tactics.v Poly.vo
Tactics.vio: Tactics.v Poly.vio
