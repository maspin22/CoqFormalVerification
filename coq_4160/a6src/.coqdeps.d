Basics.vo Basics.glob Basics.v.beautified: Basics.v
Basics.vio: Basics.v
IndPrinciplesTest.vo IndPrinciplesTest.glob IndPrinciplesTest.v.beautified: IndPrinciplesTest.v IndPrinciples.vo
IndPrinciplesTest.vio: IndPrinciplesTest.v IndPrinciples.vio
IndPrinciples.vo IndPrinciples.glob IndPrinciples.v.beautified: IndPrinciples.v ProofObjects.vo
IndPrinciples.vio: IndPrinciples.v ProofObjects.vio
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
ProofObjectsTest.vo ProofObjectsTest.glob ProofObjectsTest.v.beautified: ProofObjectsTest.v ProofObjects.vo
ProofObjectsTest.vio: ProofObjectsTest.v ProofObjects.vio
ProofObjects.vo ProofObjects.glob ProofObjects.v.beautified: ProofObjects.v IndProp.vo
ProofObjects.vio: ProofObjects.v IndProp.vio
Tactics.vo Tactics.glob Tactics.v.beautified: Tactics.v Poly.vo
Tactics.vio: Tactics.v Poly.vio
