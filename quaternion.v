(* coq-robot (c) 2017 AIST and INRIA. License: LGPL v3. *)
From mathcomp Require Import all_ssreflect ssralg ssrint.
From mathcomp Require Import ssrnum rat poly closed_field polyrcf matrix.
From mathcomp Require Import mxalgebra tuple mxpoly zmodp binomial realalg.
From mathcomp Require Import complex finset fingroup perm.

(*
1. section quaternion
  - definition of quaternions
  - definition of addition, negation -> quaternions form a zmodtype
  - definition of multiplication -> quaternions form a ring
  - definition of scaling -> quaternions form a lmodtype
  - definition of inverse -> quaternions form a unitringtype
  - definition of conjugate, norm
  - definition of unit quaternions
*)

Reserved Notation "x %:q" (at level 2, format "x %:q").
Reserved Notation "x %:v" (at level 2, format "x %:v").
Reserved Notation "Q '`0'" (at level 1, format "Q '`0'").
Reserved Notation "Q '`1'" (at level 1, format "Q '`1'").
Reserved Notation "Q '_i'" (at level 1, format "Q '_i'").
Reserved Notation "Q '_j'" (at level 1, format "Q '_j'").
Reserved Notation "Q '_k'" (at level 1, format "Q '_k'").
Reserved Notation "'`i'".
Reserved Notation "'`j'".
Reserved Notation "'`k'".
Reserved Notation "x '^*q'" (at level 2, format "x '^*q'").
Reserved Notation "a *`i" (at level 3).
Reserved Notation "a *`j" (at level 3).
Reserved Notation "a *`k" (at level 3).
Reserved Notation "x '^*dq'" (at level 2, format "x '^*dq'").

Declare Scope quat_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Section quaternion0.
Variable R : ringType.

Record quat := mkQuat {quatl : R ; quati : R ; quatj : R; quatk : R}.

Definition mkQuatq x := (mkQuat x 0 0 0).
Local Notation "x %:q" := (mkQuatq x).
Definition mkQuatv (x : 'rV[R]_3) := mkQuat 0 (x 0 0) (x 0 1) (x 0 2%:R).

Local Notation "x %:v" := (mkQuatv x).
Local Notation "'`i'" := (mkQuat 0 1 0 0).
Local Notation "'`j'" := (mkQuat 0 0 1 0).
Local Notation "'`k'" := (mkQuat 0 0 0 1).
Local Notation "Q '`0'" := (quatl Q).
Local Notation "Q '_i'" := (quati Q).
Local Notation "Q '_j'" := (quatj Q).
Local Notation "Q '_k'" := (quatk Q).

Definition quadruple_of_quat (a : quat) := 
  let: mkQuat a0 a1 a2 a3 := a in (a0, a1, a2, a3).
Definition quat_of_quadruple (x : R * R * R * R) := 
    let: (x0, x1, x2, x3) := x in mkQuat x0 x1 x2 x3.

Lemma quat_of_quadrupleK : cancel quadruple_of_quat quat_of_quadruple.
Proof. by case. Qed.

Definition quat_eqMixin := CanEqMixin quat_of_quadrupleK.
Canonical Structure quat_eqType := EqType quat quat_eqMixin.
Definition quat_choiceMixin := CanChoiceMixin quat_of_quadrupleK.
Canonical Structure quat_choiceType := ChoiceType quat quat_choiceMixin.

Lemma eq_quat (a b : quat) : (a == b) = 
    [&& a`0 == b`0, a _i == b _i, a _j == b _j & a _k == b _k].
Proof.
case: a b => [a0 a1 a2 a3] [b0 b1 b2 b3] /=.
by apply/idP/idP => [/eqP [-> -> -> ->] |
                     /and4P[/eqP -> /eqP -> /eqP -> /eqP ->]]; rewrite ?eqxx.
Qed.

Definition addq (a b : quat) := 
  mkQuat (a`0 + b`0) (a _i + b _i) (a _j + b _j) (a _k + b _k).

Lemma addqC : commutative addq.
Proof. by move=> *; congr mkQuat; rewrite addrC. Qed.

Lemma addqA : associative addq.
Proof. by move=> *; congr mkQuat; rewrite addrA. Qed.

Lemma add0q : left_id 0%:q addq.
Proof. by case=> *; congr mkQuat; rewrite add0r. Qed.

Definition oppq (a : quat) := mkQuat (- a`0) (- a _i) (- a _j) (- a _k).

Lemma addNq : left_inverse 0%:q oppq addq.
Proof. by move=> *; congr mkQuat; rewrite addNr. Qed.

Definition quat_ZmodMixin := ZmodMixin addqA addqC add0q addNq.
Canonical quat_ZmodType := ZmodType quat quat_ZmodMixin.

Lemma addqE (a b : quat) : a + b = addq a b. Proof. by []. Qed.

Lemma oppqE (a : quat) : - a = oppq a. Proof. by []. Qed.

Local Notation "a *`i" := (mkQuat 0 a 0 0) (at level 3).
Local Notation "a *`j" := (mkQuat 0 0 a 0) (at level 3).
Local Notation "a *`k" := (mkQuat 0 0 0 a) (at level 3).

Lemma quatE (a : quat) : a = (a`0)%:q + a _i *`i + a _j *`j + a _k *`k.
Proof.
apply/eqP; rewrite eq_quat /= !addr0 eqxx /= add0r.
by case: a => /= a0 ai aj ak; rewrite !add0r !eqxx.
Qed.

Lemma quat_scalarE (a b : R) : (a%:q == b%:q) = (a == b).
Proof. by apply/idP/idP => [/eqP[] ->|/eqP -> //]. Qed.

Lemma quat_realD (x y : R) : (x + y)%:q = x%:q + y%:q.
Proof. by rewrite addqE /addq /= addr0. Qed.

Lemma quat_vectD (x y : 'rV[R]_3) : (x + y)%:v = x%:v + y%:v.
Proof.  by apply/eqP; rewrite eq_quat /= !mxE ?add0r !eqxx. Qed.

End quaternion0.

Delimit Scope quat_scope with quat.
Local Open Scope quat_scope.

Notation "x %:q" := (mkQuatq x).
Notation "x %:v" := (mkQuatv x).
Notation "'`i'" := (mkQuat 0 1 0 0).
Notation "'`j'" := (mkQuat 0 0 1 0).
Notation "'`k'" := (mkQuat 0 0 0 1).
Notation "Q '`0'" := (quatl Q).
Notation "Q '_i'" := (quati Q).
Notation "Q '_j'" := (quatj Q).
Notation "Q '_k'" := (quatk Q).
Definition quat_row (R: ringType) (a : quat R) :=
  \row_(i < 3) (if i == 0 then a _i else if i == 1 then a _j else a _k).
Notation "Q '`1'" := (quat_row Q). 
Notation "a *`i" := (mkQuat 0 a 0 0) (at level 3).
Notation "a *`j" := (mkQuat 0 0 a 0) (at level 3).
Notation "a *`k" := (mkQuat 0 0 0 a) (at level 3).

Section quaternion.
Variable R : comRingType.

Definition mulq (a b : quat R) :=
  mkQuat (a`0 * b`0 - a _i * b _i - a _j * b _j - a _k * b _k)
         (a`0 * b _i + a _i * b`0 + a _j * b _k - a _k * b _j)
         (a`0 * b _j - a _i * b _k + a _j * b`0 + a _k * b _i)
         (a`0 * b _k + a _i * b _j - a _j * b _i + a _k * b`0).

(* To get ring *)
Let ms := (GRing.ComRing.sort R).
Let me : ms -> ms -> Prop := @eq ms.
Let ma : ms -> ms -> ms := @GRing.add _.
Let mm : ms -> ms -> ms := @GRing.mul _.
Let mo : ms -> ms := @GRing.opp _.
Let mz : ms := @GRing.zero _.
Let mone : ms := @GRing.one _.

Let Rring : 
  ring_theory mz mone ma mm (fun x y => ma x (mo y)) mo me :=
  mk_rt mz mone ma mm _ mo me (@add0r _) (@addrC _) (@addrA _) (@mul1r _)
  (@mulrC _) (@mulrA _) (@mulrDl _) (fun _ _ => refl_equal _) (@subrr _).

Add Ring rR : Rring.

Ltac rring := rewrite -/me -/ma -/mm -/mo -/mone -/mz; ring.

Lemma mulqA : associative mulq.
Proof.
by move=> [a0 ai aj ak] [b0 bi bj bk] [c0 ci cj ck]; congr mkQuat => /=; rring.
Qed.

Lemma mul1q : left_id 1%:q mulq.
Proof.
by move=> [a0 ai aj ak]; congr mkQuat => /=; rring.
Qed.

Lemma mulq1 : right_id 1%:q mulq.
Proof.
by move=> [a0 ai aj ak]; congr mkQuat => /=; rring.
Qed.

Lemma mulqDl : left_distributive mulq (@addq R).
Proof.
by move=> [a0 ai aj ak] [b0 bi bj bk] [c0 ci cj ck]; congr mkQuat => /=; rring.
Qed.

Lemma mulqDr : right_distributive mulq (@addq R).
Proof.
by move=> [a0 ai aj ak] [b0 bi bj bk] [c0 ci cj ck]; congr mkQuat => /=; rring.
Qed.

Lemma oneq_neq0 : 1%:q != 0 :> quat R.
Proof. apply/eqP => -[]; apply/eqP. exact: oner_neq0. Qed.

Definition quat_RingMixin :=
  RingMixin mulqA mul1q mulq1 mulqDl mulqDr oneq_neq0.
Canonical Structure quat_Ring := Eval hnf in RingType (quat R) quat_RingMixin.

Lemma mulqE a b : a * b = mulq a b. Proof. done. Qed.

Lemma quat_realM (x y : R) : (x * y)%:q = x%:q * y%:q.
Proof. by congr mkQuat => /=; rring. Qed.

Lemma iiN1 : `i * `i = -1.
Proof. by congr mkQuat => /=; rring. Qed.

Lemma ikNj : `i * `k = - `j.
Proof. by congr mkQuat => /=; rring. Qed.

Definition scaleq k (a : quat R) :=
  mkQuat (k * a`0) (k * a _i) (k * a _j) (k * a _k).

Lemma scaleqA a b w : scaleq a (scaleq b w) = scaleq (a * b) w.
Proof. by congr mkQuat => /=; rring. Qed.

Lemma scaleq1 : left_id 1 scaleq.
Proof. by case => *; congr mkQuat => /=; rring. Qed.

Lemma scaleqDr : @right_distributive R (quat R) scaleq +%R.
Proof. by move=> k x y; case: x; case: y => *; congr mkQuat => /=; rring. Qed.

Lemma scaleqDl w : {morph (scaleq^~ w : R -> quat R) : a b / a + b}.
Proof. by move=> k1 k2; case: w => *; congr mkQuat => /=; rring. Qed.

Definition quat_lmodMixin := LmodMixin scaleqA scaleq1 scaleqDr scaleqDl.
Canonical quat_lmodType := Eval hnf in LmodType R (quat R) quat_lmodMixin.

Lemma scaleqE (k : R) (a : quat R) :
  k *: a = 
  k *: (a `0) %:q + k *: (a _i) *`i + k *: (a _j) *`j + k *: (a _k) *`k.
Proof. by congr mkQuat => /=; rring. Qed.

Lemma quatlE a : a %:q = a *: (1 : quat R).
Proof. by congr mkQuat; rewrite !(mulr0, mulr1). Qed.

Lemma ijk : `i * `j = `k :> quat R.
Proof. by congr mkQuat => /=; rring. Qed.

End quaternion.

Section quaternion1.
Variable R : rcfType.

(* To get ring *)
Let ms := (GRing.ComRing.sort R).
Let me : ms -> ms -> Prop := @eq ms.
Let ma : ms -> ms -> ms := @GRing.add _.
Let mm : ms -> ms -> ms := @GRing.mul _.
Let mo : ms -> ms := @GRing.opp _.
Let mz : ms := @GRing.zero _.
Let mone : ms := @GRing.one _.

Let Rring : 
  ring_theory mz mone ma mm (fun x y => ma x (mo y)) mo me :=
  mk_rt mz mone ma mm _ mo me (@add0r _) (@addrC _) (@addrA _) (@mul1r _)
  (@mulrC _) (@mulrA _) (@mulrDl _) (fun _ _ => refl_equal _) (@subrr _).

Add Ring rR : Rring.

Ltac rring := rewrite -/me -/ma -/mm -/mo -/mone -/mz; ring.


Definition sqrq (a : quat R) := a`0 ^+ 2 + a _i ^+ 2 + a _j ^+ 2 + a _k ^+ 2.

Lemma sqrq_eq0 a : (sqrq a == 0) = (a == 0).
Proof.
case: a => a0 ai aj ak /=; apply/idP/idP; last first.
 by case/eqP => -> -> -> ->; rewrite /sqrq /= !expr0n !add0r.
by rewrite !paddr_eq0 ?addr_ge0 ?sqr_ge0 ?sqrf_eq0 //= -!andbA =>
  /and4P[/eqP-> /eqP-> /eqP-> /eqP->].
Qed.

Definition conjq (a : quat R) := mkQuat (a`0) (- a _i) (- a _j) (- a _k).
Local Notation "x '^*q'" := (conjq x).

Lemma conjq_linear : linear conjq.
Proof.
by move=> k [a0 ai aj ak] [b0 bi bj bk] /=; congr mkQuat;
   rewrite /= !mulrN opprD.
Qed.

Canonical conjq_is_additive := Additive conjq_linear.
Canonical conjq_is_linear := AddLinear conjq_linear.

Lemma conjqI a : (a^*q)^*q = a.
Proof. by case: a => a0 ai aj ak; congr mkQuat; rewrite opprK. Qed.

Lemma conjq0 : 0^*q = 0.
Proof. by congr mkQuat; rewrite /= oppr0. Qed.

Lemma conjqP a : a * a^*q = (sqrq a)%:q.
Proof.
by case: a => *; congr mkQuat; rewrite /sqrq /= ?expr2; rring.
Qed.

Lemma conjqM a b : (a * b)^*q = b^*q * a^*q.
Proof.
by case: a b => [a0 ai aj ak] [b0 bi bj bk]; congr mkQuat => /=; rring.
Qed.

Lemma conjqE a :
  a^*q = - (1 / 2%:R) *: (a + `i * a * `i + `j * a * `j + `k * a * `k).
Proof.
apply: etrans (_ : - (1 / 2%:R) *: (- a^*q - a^*q)  = _).
  rewrite -mulr2n -scaler_nat scaleNr scalerA mul1r mulVf ?pnatr_eq0 //.
  by rewrite scale1r opprK.
by congr (- _ *: _); case: a => *; congr mkQuat => /=; rring.
Qed.

Lemma conjq_scalar a : (a`0)%:q = (1 / 2%:R) *: (a + a^*q).
Proof.
apply: etrans (_ : (1 / 2%:R) *: ((a`0)%:q + (a`0)%:q)  = _).
  by rewrite -mulr2n -scaler_nat scalerA mul1r mulVf ?pnatr_eq0 // scale1r.
by congr (_ *: _); case: a => *; congr mkQuat => /=; rring.
Qed.

Lemma conjq_vector a : (a`1)%:v = (1 / 2%:R) *: (a - a^*q).
Proof.
apply: etrans (_ : (1 / 2%:R) *: ((a`1)%:v + (a`1)%:v)  = _).
  by rewrite -mulr2n -scaler_nat scalerA mul1r mulVf ?pnatr_eq0 // scale1r.
rewrite /mkQuatv /=.
by congr (_ *: _); case: a => *; congr mkQuat; rewrite ?mxE /=; rring.
Qed.

Definition invq a := (1 / sqrq a) *: (a ^*q).

Definition unitq : pred (quat R) := [pred a | a != 0].

Lemma mulVq : {in unitq, left_inverse 1 invq (@mulq R)}.
Proof.
move=> a aH.
apply: etrans (_ : (1 / sqrq a) *: (sqrq a)%:q = _); last first.
  by rewrite quatlE scalerA mul1r mulVf ?scale1r // sqrq_eq0.
case: a aH => a0 ai aj ak; rewrite /sqrq inE /= => aH.
congr mkQuat; rewrite /= /sqrq /= !expr2; rring.
Qed.

Lemma mulqV : {in unitq, right_inverse 1 invq (@mulq R)}.
Proof.
move=> a aH.
apply: etrans (_ : (1 / sqrq a) *: (sqrq a)%:q = _); last first.
  by rewrite quatlE scalerA mul1r mulVf ?scale1r // sqrq_eq0.
case: a aH => a0 ai aj ak; rewrite /sqrq inE /= => aH.
congr mkQuat; rewrite /= /sqrq /= !expr2; rring.
Qed.

Lemma quat_integral (x y : quat R) : (x * y == 0) = ((x == 0) || (y == 0)).
Proof.
case: (x =P 0) => [->|/eqP xNZ] /=; first by rewrite mul0r eqxx.
apply/eqP/eqP => [|->]; last by rewrite mulr0.
move=> H.
by rewrite -[y]mul1r -(@mulVq x) // -mulrA H mulr0.
Qed.

Lemma unitqP a b : b * a = 1 /\ a * b = 1 -> unitq a.
Proof.
move=> [ba1 ab1]; rewrite /unitq inE; apply/eqP => x0.
move/esym: ab1; rewrite x0 mul0r.
apply/eqP; exact: oneq_neq0.
Qed.

Lemma invq0id : {in [predC unitq], invq =1 id}.
Proof.
move=> a; rewrite !inE negbK => /eqP ->.
by rewrite /invq /= conjq0 scaler0.
Qed.

Definition quat_UnitRingMixin := UnitRingMixin mulVq mulqV unitqP invq0id.
Canonical quat_unitRing := UnitRingType (quat R) quat_UnitRingMixin.

Lemma invqE a : a^-1 = invq a. Proof. by []. Qed.

Definition normq (a : quat R) : R := Num.sqrt (sqrq a).

Lemma normq0 : normq 0 = 0.
Proof. by rewrite /normq /sqrq expr0n /= !addr0 sqrtr0. Qed.

Lemma normqc a : normq a^*q = normq a.
Proof. by rewrite /normq /sqrq /= !sqrrN. Qed.

Lemma normqE a : (normq a ^+ 2)%:q = a^*q * a.
Proof.
rewrite -normqc /normq sqr_sqrtr; last by rewrite /sqrq !addr_ge0 // sqr_ge0.
by rewrite -conjqP conjqI.
Qed.

Lemma normq_ge0 a : normq a >= 0.
Proof. by apply sqrtr_ge0. Qed.

Lemma normq_eq0 a : (normq a == 0) = (a == 0).
Proof.
rewrite /normq /sqrq -sqrtr0 eqr_sqrt //; last by rewrite !addr_ge0 // sqr_ge0.
by rewrite  -[_ + _]/(sqrq _) sqrq_eq0.
Qed.

Lemma quatAl k (a b : quat R) : k *: (a * b) = k *: a * b.
Proof.
by case: a b => [a0 ai aj ak] [b0 bi bj bk]; congr mkQuat => /=; rring.
Qed.

Canonical quat_lAlgType := Eval hnf in LalgType _ (quat R) quatAl.

Lemma quatAr k (a b : quat R) : k *: (a * b) = a * (k *: b).
Proof.
by case: a b => [a0 ai aj ak] [b0 bi bj bk]; congr mkQuat => /=; rring.
Qed.

Canonical quat_algType := Eval hnf in AlgType _ (quat R) quatAr.

Lemma quat_algE x : x%:q = x%:A.
Proof. exact: quatlE. Qed.

Lemma normqM (Q P : quat R) : normq (Q * P) = normq Q * normq P.
Proof.
apply/eqP; rewrite -(@eqr_expn2 _ 2) // ?normq_ge0 //; last first.
  by rewrite mulr_ge0 // normq_ge0.
rewrite -quat_scalarE normqE conjqM -mulrA (mulrA (Q^*q)) -normqE.
rewrite quat_algE mulr_algl -scalerAr exprMn quat_realM.
by rewrite (normqE P) -mulr_algl quat_algE.
Qed.

Lemma normqZ (k : R) (q : quat R) : normq (k *: q) = `|k| * normq q.
Proof.
by rewrite /normq /sqrq /= !exprMn -!mulrDr sqrtrM ?sqr_ge0 // sqrtr_sqr.
Qed.

Lemma normqV (q : quat R) : normq (q^-1) = normq q / sqrq q.
Proof.
rewrite invqE /invq normqZ ger0_norm; last first.
  by rewrite divr_ge0 // ?ler01 // /sqrq !addr_ge0 // sqr_ge0.
by rewrite normqc mulrC mul1r.
Qed.

Definition normQ Q := (normq Q)%:q.

Lemma normQ_eq0 x : (normQ x == 0) = (x == 0).
Proof. by rewrite /normQ quat_scalarE normq_eq0. Qed.

Definition normalizeq (q : quat R) : quat R := 1 / normq q *: q.

Lemma normalizeq1 (q : quat R) : q != 0 -> normq (normalizeq q) = 1.
Proof.
move=> q0.
rewrite /normalizeq normqZ normrM normr1 mul1r normrV; last by rewrite unitfE normq_eq0.
by rewrite ger0_norm ?normq_ge0 // mulVr // unitfE normq_eq0.
Qed.

Definition lequat (Q P : quat R) :=
  let: mkQuat Q0 Qi Qj Qk := Q in let: mkQuat P0 Pi Pj Pk := P in
  [&& Q0 <= P0, Qi == Pi, Qj == Pj & Qk == Pk].

Lemma lequat_normD (x y : quat R) : lequat (normQ (x + y)) (normQ x + normQ y).
Proof.
rewrite /normQ !quatlE -scalerDl.
apply/and4P; rewrite !mulr0 ?mulr1 eqxx; split => //.
rewrite /normq /sqrq /=.
have sqr_normE (x1 : R) : `|x1| ^+2 = x1 ^+ 2.
  by case: (ltrgt0P x1); rewrite ?sqrrN // => ->.
have ler_mul_norm (x1 y1 : R) : x1 * y1 <= `|x1| * `|y1|.
  rewrite {1}(numEsign x1) {1}(numEsign y1) mulrAC mulrA -signr_addb.
  rewrite -mulrA [_ * `|x1|]mulrC.
  case: (_ (+) _); rewrite !(expr0, expr1, mulNr, mul1r) //.
  rewrite -subr_gte0 opprK -mulr2n; apply: mulrn_wge0.
  by apply: mulr_ge0; apply: normr_ge0.
have ler_exprD (x1 y1 : R) : (x1 + y1) ^+ 2 <= (`|x1| + `|y1|) ^+ 2.
  rewrite !sqrrD // !sqr_normE.
  by repeat apply: ler_add.
apply: le_trans 
  (_ : Num.sqrt
        ((`|x`0| + `|y`0|) ^+ 2 + (`|x _i| + `|y _i|) ^+ 2 + 
         (`|x _j| + `|y _j|) ^+ 2 + (`|x _k| + `|y _k|) ^+ 2)
         <= _).
  rewrite -ler_sqr ?nnegrE; last 2 first.
  - by apply: sqrtr_ge0.
  - by apply: sqrtr_ge0.
  rewrite !sqr_sqrtr; last 2 first.
  - by repeat apply: addr_ge0; rewrite sqr_ge0.
  - by repeat apply: addr_ge0; rewrite sqr_ge0.
  by repeat apply: ler_add; apply: ler_exprD.
rewrite -(sqr_normE x`0) -(sqr_normE y`0).
rewrite  -(sqr_normE (x _i)) -(sqr_normE (y _i)).
rewrite -(sqr_normE (x _j)) -(sqr_normE (y _j)).
rewrite -(sqr_normE (x _k)) -(sqr_normE (y _k)).
set x0 := `|_|; set y0 := `|_|; set x1 := `|_|; set y1 := `|_|.
set x2 := `|_|; set y2 := `|_|; set x3 := `|_|; set y3 := `|_|.
rewrite -ler_sqr ?nnegrE; last 2 first.
- by apply: sqrtr_ge0.
- by apply: addr_ge0; apply: sqrtr_ge0.
rewrite [in X in _ <= X]sqrrD !sqr_sqrtr; last 3 first.
- by repeat apply: addr_ge0; rewrite sqr_ge0.
- by repeat apply: addr_ge0; rewrite sqr_ge0.
- by repeat apply: addr_ge0; rewrite sqr_ge0.
have -> : 
       (x0 + y0) ^+ 2 + (x1 + y1) ^+ 2 + (x2 + y2) ^+ 2 + (x3 + y3) ^+ 2 =
       x0 ^+ 2 + x1 ^+ 2 + x2 ^+ 2 + x3 ^+ 2 +
      ((x0 * y0) + (x1 * y1) + (x2 * y2) + (x3 * y3)) *+ 2 +
       (y0 ^+ 2 + y1 ^+ 2 + y2 ^+ 2 + y3 ^+ 2).
  by rewrite !expr2 mulr2n; rring.
apply: ler_add => //.
apply: ler_add => //.
rewrite ler_muln2r /=.
rewrite -ler_sqr ?nnegrE; last 2 first.
- by repeat apply: addr_ge0; apply: mulr_ge0; apply: normr_ge0.
- by apply: mulr_ge0; apply: sqrtr_ge0.
rewrite exprMn !sqr_sqrtr; last 2 first.
- by repeat apply: addr_ge0; rewrite sqr_ge0.
- by repeat apply: addr_ge0; rewrite sqr_ge0.
(* This is Cauchy Schwartz *)
rewrite -[_ <= _]orFb -[false]/(2 == 0)%nat.
rewrite -ler_muln2r.
pose xl := [:: x0; x1; x2; x3]; pose yl := [:: y0; y1; y2; y3].
pose u := \sum_(i < 4) \sum_(j < 4)
           (xl`_i * yl`_j - xl`_j * yl`_i) ^+ 2.
set z1 := _ *+ 2; set z2 := _ *+ 2.
suff ->: z2 = z1 + u.
  rewrite -{1}(addr0 z1).
  apply: ler_add => //.
  rewrite /u !big_ord_recr /= !big_ord0 !add0r.
  by repeat apply: addr_ge0; rewrite sqr_ge0.
rewrite /z2 /z1 /u.
rewrite !big_ord_recr /= !big_ord0 !add0r !mulr2n !expr2.
rring.
Qed.

Definition ltquat (Q P : quat R) :=
  let: mkQuat Q0 Qi Qj Qk := Q in let: mkQuat P0 Pi Pj Pk := P in
  [&& Q0 < P0, Qi == Pi, Qj == Pj & Qk == Pk].

Lemma ltquat0_add x y : ltquat 0 x -> ltquat 0 y -> ltquat 0 (x + y).
Proof.
case: x => x0 xi xj xk ; case: y => y0 yi yj yk /=.
case/and4P => x0P /eqP<- /eqP<- /eqP<-.
case/and4P => y0P /eqP<- /eqP<- /eqP<-.
rewrite !addr0 eqxx !andbT.
by apply: addr_gt0.
Qed.

Lemma ge0_lequat_total x y :
  lequat 0 x -> lequat 0 y -> lequat x y || lequat y x.
Proof.
case: x => x0 xi xj xk ; case: y => y0 yi yj yk /=.
case/and4P => x0P /eqP<- /eqP<- /eqP<-.
case/and4P => y0P /eqP<- /eqP<- /eqP<-.
rewrite eqxx !andbT.
case:  (lerP x0 y0) => //=.
by apply: ltW.
Qed.

Lemma normQM x y : normQ (x * y) = normQ x * normQ y.
Proof. by rewrite {1}/normQ normqM quat_realM. Qed.

Lemma lequat_def x y : lequat x y = (normQ (y - x) == y - x).
Proof.
rewrite /lequat /normQ /normq /sqrq.
case: x => x0 xi xj xk ; case: y => y0 yi yj yk /=.
apply/idP/idP.
  case/and4P => x0Ly0 /eqP<- /eqP<- /eqP<-.
  apply/eqP; congr mkQuat; rewrite ?subrr ?expr0n ?addr0 //=.
  rewrite sqrtr_sqr.
  by apply/eqP; rewrite eqr_norm_id subr_ge0.
case/eqP => /eqP H1 H2 H3 H4.
rewrite -H4 -H3 -H2 ?expr0n ?addr0 sqrtr_sqr eqr_norm_id in H1.
rewrite eq_sym -subr_eq0 -H2 eq_sym eqxx andTb.
rewrite -subr_eq0 -H3 eq_sym eqxx andTb.
by rewrite -subr_eq0 -H4 eqxx andbT -subr_ge0.
Qed.

Lemma ltquat_def x y : ltquat x y = (y != x) && lequat x y.
Proof.
case: x => x0 xi xj xk ; case: y => y0 yi yj yk /=.
apply/and4P/andP => [[x0Ly0 /eqP<- /eqP<- /eqP<-] | ].
  rewrite !eqxx !andbT; split.
    by apply/negP; case/eqP => y0E; rewrite y0E // ltxx in x0Ly0.
  by apply: ltW.
rewrite eq_quat /=.
case=> H1 H2; move: H1; case/and4P: H2 => x0Ly0 /eqP<- /eqP<- /eqP<-.
rewrite !eqxx !andbT => y0Dx0.
split => //.
by rewrite lt_neqAle eq_sym y0Dx0.
Qed.

Fail Definition quat_POrderedMixin := NumMixin lequat_normD ltquat0_add
 eq0_normQ ge0_lequat_total normQM lequat_def ltquat_def.
Fail Canonical Structure quat_numDomainType :=
  NumDomainType _ quat_POrderedMixin.

Definition uquat := [qualify x : quat R | normq x == 1].
Fact uquat_key : pred_key uquat. Proof. by []. Qed.
Canonical uquat_keyed := KeyedQualifier uquat_key.

Lemma uquatE a : (a \is uquat) = (normq a == 1).
Proof. done. Qed.

Lemma uquatE' (q : quat R) : (q \is uquat) = (sqrq q == 1).
Proof.
apply/idP/idP => [qu|].
  rewrite -eqr_sqrt ?ler01 //.
    rewrite uquatE in qu; by rewrite -/(normq q) (eqP qu) sqrtr1.
  by rewrite /sqrq !addr_ge0 // sqr_ge0.
rewrite uquatE /normq => /eqP ->; by rewrite sqrtr1.
Qed.

Lemma muluq_proof a b : a \is uquat -> b \is uquat -> a * b \is uquat.
Proof. rewrite 3!uquatE => /eqP Hq /eqP Hp; by rewrite normqM Hq Hp mulr1. Qed.

Lemma invuq_proof a : a \is uquat -> normq (a^-1) == 1.
Proof.
move=> Hq; rewrite normqV.
move: (Hq); rewrite uquatE => /eqP ->.
move: Hq; rewrite uquatE' => /eqP ->.
by rewrite invr1 mulr1.
Qed.

Lemma invq_uquat a : a \is uquat -> a^-1 = a^*q.
Proof.
rewrite uquatE' => /eqP Hq; by rewrite invqE /invq Hq invr1 mul1r scale1r.
Qed.

Let vector := 'rV[R]_3.

Definition quat_rot (a : quat R) (v : vector) : quat R :=
  (a : quat R) * v%:v * a^*q.


Definition pureq (q : quat R) : bool := q`0 == 0.

Lemma quat_rot_is_vector a v : pureq (quat_rot a v).
Proof.
rewrite /pureq /quat_rot /=; apply/eqP.
set x1 := v _ _; set x2 := v _ _; set x3 := v _ _.
set x4 := _ `0; set x5 := _ _i; set x6 := _ _j; set x7 := _ _k.
rring.
Qed.

Lemma quat_rot_is_linear a : linear (fun v => (quat_rot a v)`1).
Proof.
move=> k x y.
apply/matrixP => i j; rewrite !mxE.
by repeat case: eqP => [_|_]; 
  case: a => a0 ai aj ak; rewrite /= !mxE;
  set x1 := x _ _; set x2 := x _ _; set x3 := x _ _;
  set y1 := y _ _; set y2 := y _ _; set y3 := y _ _;
  rring.
Qed.

Lemma quat_rot_is_linearE q v :
  Linear (quat_rot_is_linear q) v = (quat_rot q v)`1.
Proof. by []. Qed.

Lemma quat_rot_axis q k : q \is uquat -> quat_rot q (k *: q`1) = (k *: q`1)%:v.
Proof.
case: q => q0 qi qj qk => /=.
rewrite uquatE' /sqrq => /eqP /= q_is_uquat.
congr mkQuat; rewrite /mkQuatv !mxE /=.
- by rring.
- by rewrite -[RHS]mul1r -q_is_uquat !expr2; rring.
- by rewrite -[RHS]mul1r -q_is_uquat !expr2; rring.
by rewrite -[RHS]mul1r -q_is_uquat !expr2; rring.
Qed.

End quaternion1.

Notation "x '^*q'" := (conjq x) : quat_scope.
