Basics.vo Basics.glob Basics.v.beautified: Basics.v
Basics.vio: Basics.v
IndPropTest.vo IndPropTest.glob IndPropTest.v.beautified: IndPropTest.v IndProp.vo
IndPropTest.vio: IndPropTest.v IndProp.vio
IndProp.vo IndProp.glob IndProp.v.beautified: IndProp.v Logic.vo
IndProp.vio: IndProp.v Logic.vio
Induction.vo Induction.glob Induction.v.beautified: Induction.v Basics.vo
Induction.vio: Induction.v Basics.vio
Lists.vo Lists.glob Lists.v.beautified: Lists.v Induction.vo
Lists.vio: Lists.v Induction.vio
Logic.vo Logic.glob Logic.v.beautified: Logic.v Tactics.vo
Logic.vio: Logic.v Tactics.vio
Poly.vo Poly.glob Poly.v.beautified: Poly.v Lists.vo
Poly.vio: Poly.v Lists.vio
Tactics.vo Tactics.glob Tactics.v.beautified: Tactics.v Poly.vo
Tactics.vio: Tactics.v Poly.vio
