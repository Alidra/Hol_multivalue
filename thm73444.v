Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm73444_term_abbrevs.
Require Import NUM_REP_INDUCT_spec.
Require Import NUM_REP_RULES_spec.
Require Import SUC_DEF_spec.
Require Import ZERO_DEF_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm71261_spec.
Lemma lem72974 (r : ind) (h1 : (NUM_REP r) = ((term0 r) = r)) : (NUM_REP r) = ((term0 r) = r).
Proof. exact (h1). Qed.
Lemma lem72975 (r : ind) (h1 : (NUM_REP r) = ((term0 r) = r)) : ((term0 r) = r) = (NUM_REP r).
Proof. exact (SYM (@lem72974 r h1)). Qed.
Lemma lem72976 (r : ind) (h1 : ((term0 r) = r) = (NUM_REP r)) : ((term0 r) = r) = (NUM_REP r).
Proof. exact (h1). Qed.
Lemma lem72977 (r : ind) (h1 : ((term0 r) = r) = (NUM_REP r)) : (NUM_REP r) = ((term0 r) = r).
Proof. exact (SYM (@lem72976 r h1)). Qed.
Lemma lem72978 (r : ind) : ((NUM_REP r) = ((term0 r) = r)) = (((term0 r) = r) = (NUM_REP r)).
Proof. exact (prop_ext (fun h1 : (NUM_REP r) = ((term0 r) = r) => @lem72975 r h1) (fun h1 : ((term0 r) = r) = (NUM_REP r) => @lem72977 r h1)). Qed.
Lemma lem72980 (n : nat) : term1 n.
Proof. exact (@lem71593 n). Qed.
Lemma lem72981 (n : nat) : (term1 n) = ((S n) = (term2 n)).
Proof. exact (eq_refl (term1 n)). Qed.
Lemma lem72983 : term3.
Proof. exact (proj2 (@lem71256)). Qed.
Lemma lem72984 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem72985 (i : ind) (h1 : term3) : term4 i.
Proof. exact (@lem72984 h1 i). Qed.
Lemma lem72986 (i : ind) : (term4 i) = (term5 i).
Proof. exact (eq_refl (term4 i)). Qed.
Lemma lem72987 (i : ind) (h1 : term3) : term5 i.
Proof. exact (EQ_MP (@lem72986 i) (@lem72985 i h1)). Qed.
Lemma lem72988 (i : ind) (h1 : NUM_REP i) : NUM_REP i.
Proof. exact (h1). Qed.
Lemma lem72989 (i : ind) (h1 : term3) (h2 : NUM_REP i) : term6 i.
Proof. exact (@lem72987 i h1 (@lem72988 i h2)). Qed.
Lemma lem72990 (i : ind) (h1 : NUM_REP i) : term7 i.
Proof. exact (fun h0 : term3 => @lem72989 i h0 h1). Qed.
Lemma lem72991 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem72992 (i : ind) (h1 : term3) (h2 : NUM_REP i) : term6 i.
Proof. exact (@lem72990 i h2 (@lem72991 h1)). Qed.
Lemma lem72993 (i : ind) (h1 : term3) : term5 i.
Proof. exact (fun h0 : NUM_REP i => @lem72992 i h1 h0). Qed.
Lemma lem72994 (h1 : term3) : term3.
Proof. exact (fun i : ind => @lem72993 i h1). Qed.
Lemma lem72995 : term8.
Proof. exact (fun h0 : term3 => @lem72994 h0). Qed.
Lemma lem72996 : term3.
Proof. exact (@lem72995 (@lem72983)). Qed.
Lemma lem72997 (i : ind) : term4 i.
Proof. exact (@lem72996 i). Qed.
Lemma lem72998 (i : ind) : (term4 i) = (term5 i).
Proof. exact (eq_refl (term4 i)). Qed.
Lemma lem73000 (h1 : 0 = (mk_num IND_0)) : 0 = (mk_num IND_0).
Proof. exact (h1). Qed.
Lemma lem73001 (h1 : 0 = (mk_num IND_0)) : (mk_num IND_0) = 0.
Proof. exact (SYM (@lem73000 h1)). Qed.
Lemma lem73002 (h1 : (mk_num IND_0) = 0) : (mk_num IND_0) = 0.
Proof. exact (h1). Qed.
Lemma lem73003 (h1 : (mk_num IND_0) = 0) : 0 = (mk_num IND_0).
Proof. exact (SYM (@lem73002 h1)). Qed.
Lemma lem73004 : (0 = (mk_num IND_0)) = ((mk_num IND_0) = 0).
Proof. exact (prop_ext (fun h1 : 0 = (mk_num IND_0) => @lem73001 h1) (fun h1 : (mk_num IND_0) = 0 => @lem73003 h1)). Qed.
Lemma lem73006 (P : nat -> Prop) : term9 P.
Proof. exact (@lem71258 (term10 P)). Qed.
Lemma lem73007 (P : nat -> Prop) : (term9 P) = (term11 P).
Proof. exact (eq_refl (term9 P)). Qed.
Lemma lem73008 (P : nat -> Prop) : term11 P.
Proof. exact (EQ_MP (@lem73007 P) (@lem73006 P)). Qed.
Lemma lem73009 (P : nat -> Prop) (h1 : term12 P) : term12 P.
Proof. exact (h1). Qed.
Lemma lem73010 (P : nat -> Prop) (h1 : term13 P) : term13 P.
Proof. exact (h1). Qed.
Lemma lem73011 (P : nat -> Prop) (h1 : P 0) : P 0.
Proof. exact (h1). Qed.
Lemma lem73018 : NUM_REP IND_0.
Proof. exact (proj1 (@lem71256)). Qed.
Lemma lem73019 : (NUM_REP IND_0) = ((NUM_REP IND_0) = True).
Proof. exact (@lem7 (NUM_REP IND_0)). Qed.
Lemma lem73021 (P : nat -> Prop) : (P 0) = ((P 0) = True).
Proof. exact (@lem7 (P 0)). Qed.
Lemma lem73035 {A B : Type'} (f : A -> B) (y : A) : (term14 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem73036 (f : ind -> Prop) (y : ind) : (term15 f y) = (f y).
Proof. exact (@lem73035 ind Prop f y). Qed.
Lemma lem73037 (P : nat -> Prop) : (term16 P) = (term17 P).
Proof. exact (@lem73036 (term10 P) IND_0). Qed.
Lemma lem73038 (P : nat -> Prop) (i : ind) : (term18 P i) = (term19 P i).
Proof. exact (eq_refl (term18 P i)). Qed.
Lemma lem73039 (P : nat -> Prop) : (term20 P) = (term10 P).
Proof. exact (fun_ext (fun i : ind => @lem73038 P i)). Qed.
Lemma lem73040 : IND_0 = IND_0.
Proof. exact (eq_refl IND_0). Qed.
Lemma lem73041 (P : nat -> Prop) : (term16 P) = (term17 P).
Proof. exact (MK_COMB (@lem73039 P) (@lem73040)). Qed.
Lemma lem73042 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem73043 (P : nat -> Prop) : (term21 P) = (term22 P).
Proof. exact (MK_COMB (@lem73042) (@lem73041 P)). Qed.
Lemma lem73044 (P : nat -> Prop) : (term17 P) = (term23 P).
Proof. exact (eq_refl (term17 P)). Qed.
Lemma lem73045 (P : nat -> Prop) : ((term16 P) = (term17 P)) = ((term17 P) = (term23 P)).
Proof. exact (MK_COMB (@lem73043 P) (@lem73044 P)). Qed.
Lemma lem73046 (P : nat -> Prop) : (term17 P) = (term23 P).
Proof. exact (EQ_MP (@lem73045 P) (@lem73037 P)). Qed.
Lemma lem73050 : (NUM_REP IND_0) = True.
Proof. exact (EQ_MP (@lem73019) (@lem73018)). Qed.
Lemma lem73051 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem73052 : term24 = (and True).
Proof. exact (MK_COMB (@lem73051) (@lem73050)). Qed.
Lemma lem73054 : (mk_num IND_0) = 0.
Proof. exact (EQ_MP (@lem73004) (@lem71415)). Qed.
Lemma lem73055 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem73056 (P : nat -> Prop) : (term25 P) = (P 0).
Proof. exact (MK_COMB (@lem73055 P) (@lem73054)). Qed.
Lemma lem73058 (P : nat -> Prop) (h1 : P 0) : (P 0) = True.
Proof. exact (EQ_MP (@lem73021 P) (@lem73011 P h1)). Qed.
Lemma lem73059 (P : nat -> Prop) (h1 : P 0) : (term25 P) = True.
Proof. exact (TRANS (@lem73056 P) (@lem73058 P h1)). Qed.
Lemma lem73060 (P : nat -> Prop) (h1 : P 0) : (term23 P) = (True /\ True).
Proof. exact (MK_COMB (@lem73052) (@lem73059 P h1)). Qed.
Lemma lem73062 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem73063 : (True /\ True) = True.
Proof. exact (@lem73062 True). Qed.
Lemma lem73064 (P : nat -> Prop) (h1 : P 0) : (term23 P) = True.
Proof. exact (TRANS (@lem73060 P h1) (@lem73063)). Qed.
Lemma lem73065 (P : nat -> Prop) (h1 : P 0) : (term17 P) = True.
Proof. exact (TRANS (@lem73046 P) (@lem73064 P h1)). Qed.
Lemma lem73066 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem73067 (P : nat -> Prop) (h1 : P 0) : (term26 P) = (and True).
Proof. exact (MK_COMB (@lem73066) (@lem73065 P h1)). Qed.
Lemma lem73075 {A B : Type'} (f : A -> B) (y : A) : (term14 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem73076 (f : ind -> Prop) (y : ind) : (term15 f y) = (f y).
Proof. exact (@lem73075 ind Prop f y). Qed.
Lemma lem73077 (P : nat -> Prop) (i : ind) : (term27 P i) = (term18 P i).
Proof. exact (@lem73076 (term10 P) i). Qed.
Lemma lem73078 (P : nat -> Prop) (i : ind) : (term18 P i) = (term19 P i).
Proof. exact (eq_refl (term18 P i)). Qed.
Lemma lem73079 (P : nat -> Prop) : (term20 P) = (term10 P).
Proof. exact (fun_ext (fun i : ind => @lem73078 P i)). Qed.
Lemma lem73080 (i : ind) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem73081 (P : nat -> Prop) (i : ind) : (term27 P i) = (term18 P i).
Proof. exact (MK_COMB (@lem73079 P) (@lem73080 i)). Qed.
Lemma lem73082 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem73083 (P : nat -> Prop) (i : ind) : (term28 P i) = (term29 P i).
Proof. exact (MK_COMB (@lem73082) (@lem73081 P i)). Qed.
Lemma lem73084 (P : nat -> Prop) (i : ind) : (term18 P i) = (term19 P i).
Proof. exact (eq_refl (term18 P i)). Qed.
Lemma lem73085 (P : nat -> Prop) (i : ind) : ((term27 P i) = (term18 P i)) = ((term18 P i) = (term19 P i)).
Proof. exact (MK_COMB (@lem73083 P i) (@lem73084 P i)). Qed.
Lemma lem73086 (P : nat -> Prop) (i : ind) : (term18 P i) = (term19 P i).
Proof. exact (EQ_MP (@lem73085 P i) (@lem73077 P i)). Qed.
Lemma lem73089 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem73090 (P : nat -> Prop) (i : ind) : (term30 P i) = (term31 P i).
Proof. exact (MK_COMB (@lem73089) (@lem73086 P i)). Qed.
Lemma lem73092 {A B : Type'} (f : A -> B) (y : A) : (term14 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem73093 (f : ind -> Prop) (y : ind) : (term15 f y) = (f y).
Proof. exact (@lem73092 ind Prop f y). Qed.
Lemma lem73094 (P : nat -> Prop) (i : ind) : (term32 P i) = (term33 P i).
Proof. exact (@lem73093 (term10 P) (IND_SUC i)). Qed.
Lemma lem73095 (P : nat -> Prop) (i : ind) : (term18 P i) = (term19 P i).
Proof. exact (eq_refl (term18 P i)). Qed.
Lemma lem73096 (P : nat -> Prop) : (term20 P) = (term10 P).
Proof. exact (fun_ext (fun i : ind => @lem73095 P i)). Qed.
Lemma lem73097 (i : ind) : (IND_SUC i) = (IND_SUC i).
Proof. exact (eq_refl (IND_SUC i)). Qed.
Lemma lem73098 (P : nat -> Prop) (i : ind) : (term32 P i) = (term33 P i).
Proof. exact (MK_COMB (@lem73096 P) (@lem73097 i)). Qed.
Lemma lem73099 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem73100 (P : nat -> Prop) (i : ind) : (term34 P i) = (term35 P i).
Proof. exact (MK_COMB (@lem73099) (@lem73098 P i)). Qed.
Lemma lem73101 (P : nat -> Prop) (i : ind) : (term33 P i) = (term36 P i).
Proof. exact (eq_refl (term33 P i)). Qed.
Lemma lem73102 (P : nat -> Prop) (i : ind) : ((term32 P i) = (term33 P i)) = ((term33 P i) = (term36 P i)).
Proof. exact (MK_COMB (@lem73100 P i) (@lem73101 P i)). Qed.
Lemma lem73103 (P : nat -> Prop) (i : ind) : (term33 P i) = (term36 P i).
Proof. exact (EQ_MP (@lem73102 P i) (@lem73094 P i)). Qed.
Lemma lem73106 (P : nat -> Prop) (i : ind) : (term37 P i) = (term38 P i).
Proof. exact (MK_COMB (@lem73090 P i) (@lem73103 P i)). Qed.
Lemma lem73109 (P : nat -> Prop) : (term39 P) = (term40 P).
Proof. exact (fun_ext (fun i : ind => @lem73106 P i)). Qed.
Lemma lem73110 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem73111 (P : nat -> Prop) : (term41 P) = (term42 P).
Proof. exact (MK_COMB (@lem73110) (@lem73109 P)). Qed.
Lemma lem73116 (P : nat -> Prop) (h1 : P 0) : (term43 P) = (term44 P).
Proof. exact (MK_COMB (@lem73067 P h1) (@lem73111 P)). Qed.
Lemma lem73118 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem73119 (P : nat -> Prop) : (term44 P) = (term42 P).
Proof. exact (@lem73118 (term42 P)). Qed.
Lemma lem73130 (P : nat -> Prop) (h1 : P 0) : (term43 P) = (term42 P).
Proof. exact (TRANS (@lem73116 P h1) (@lem73119 P)). Qed.
Lemma lem73131 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem73132 (P : nat -> Prop) (h1 : P 0) : (term45 P) = (term46 P).
Proof. exact (MK_COMB (@lem73131) (@lem73130 P h1)). Qed.
Lemma lem73140 {A B : Type'} (f : A -> B) (y : A) : (term14 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem73141 (f : ind -> Prop) (y : ind) : (term15 f y) = (f y).
Proof. exact (@lem73140 ind Prop f y). Qed.
Lemma lem73142 (P : nat -> Prop) (a : ind) : (term27 P a) = (term18 P a).
Proof. exact (@lem73141 (term10 P) a). Qed.
Lemma lem73143 (P : nat -> Prop) (i : ind) : (term18 P i) = (term19 P i).
Proof. exact (eq_refl (term18 P i)). Qed.
Lemma lem73144 (P : nat -> Prop) : (term20 P) = (term10 P).
Proof. exact (fun_ext (fun i : ind => @lem73143 P i)). Qed.
Lemma lem73145 (a : ind) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem73146 (P : nat -> Prop) (a : ind) : (term27 P a) = (term18 P a).
Proof. exact (MK_COMB (@lem73144 P) (@lem73145 a)). Qed.
Lemma lem73147 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem73148 (P : nat -> Prop) (a : ind) : (term28 P a) = (term29 P a).
Proof. exact (MK_COMB (@lem73147) (@lem73146 P a)). Qed.
Lemma lem73149 (P : nat -> Prop) (a : ind) : (term18 P a) = (term19 P a).
Proof. exact (eq_refl (term18 P a)). Qed.
Lemma lem73150 (P : nat -> Prop) (a : ind) : ((term27 P a) = (term18 P a)) = ((term18 P a) = (term19 P a)).
Proof. exact (MK_COMB (@lem73148 P a) (@lem73149 P a)). Qed.
Lemma lem73151 (P : nat -> Prop) (a : ind) : (term18 P a) = (term19 P a).
Proof. exact (EQ_MP (@lem73150 P a) (@lem73142 P a)). Qed.
Lemma lem73154 (a : ind) : (term47 a) = (term47 a).
Proof. exact (eq_refl (term47 a)). Qed.
Lemma lem73155 (P : nat -> Prop) (a : ind) : (term48 P a) = (term49 P a).
Proof. exact (MK_COMB (@lem73154 a) (@lem73151 P a)). Qed.
Lemma lem73158 (P : nat -> Prop) : (term50 P) = (term51 P).
Proof. exact (fun_ext (fun a : ind => @lem73155 P a)). Qed.
Lemma lem73159 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem73160 (P : nat -> Prop) : (term52 P) = (term53 P).
Proof. exact (MK_COMB (@lem73159) (@lem73158 P)). Qed.
Lemma lem73165 (P : nat -> Prop) (h1 : P 0) : (term11 P) = (term54 P).
Proof. exact (MK_COMB (@lem73132 P h1) (@lem73160 P)). Qed.
Lemma lem73168 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem73169 (P : nat -> Prop) (h1 : P 0) : (term55 P) = (term56 P).
Proof. exact (MK_COMB (@lem73168) (@lem73165 P h1)). Qed.
Lemma lem73170 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem73171 (n : nat) (P : nat -> Prop) (h1 : P 0) : (term57 P n) = (term58 P n).
Proof. exact (MK_COMB (@lem73169 P h1) (@lem73170 P n)). Qed.
Lemma lem73174 (n : nat) (P : nat -> Prop) (h1 : P 0) : (term58 P n) = (term57 P n).
Proof. exact (SYM (@lem73171 n P h1)). Qed.
Lemma lem73175 (P : nat -> Prop) (h1 : term42 P) : term42 P.
Proof. exact (h1). Qed.
Lemma lem73176 (i : ind) (P : nat -> Prop) (h1 : term42 P) : term59 P i.
Proof. exact (@lem73175 P h1 i). Qed.
Lemma lem73177 (P : nat -> Prop) (i : ind) : (term59 P i) = (term38 P i).
Proof. exact (eq_refl (term59 P i)). Qed.
Lemma lem73178 (i : ind) (P : nat -> Prop) (h1 : term42 P) : term38 P i.
Proof. exact (EQ_MP (@lem73177 P i) (@lem73176 i P h1)). Qed.
Lemma lem73179 (P : nat -> Prop) (i : ind) : (term38 P i) = ((term38 P i) = True).
Proof. exact (@lem7 (term38 P i)). Qed.
Lemma lem73190 (i : ind) (P : nat -> Prop) (h1 : term42 P) : (term38 P i) = True.
Proof. exact (EQ_MP (@lem73179 P i) (@lem73178 i P h1)). Qed.
Lemma lem73191 (P : nat -> Prop) (h1 : term42 P) : (term40 P) = term60.
Proof. exact (fun_ext (fun i : ind => @lem73190 i P h1)). Qed.
Lemma lem73192 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem73193 (P : nat -> Prop) (h1 : term42 P) : (term42 P) = term61.
Proof. exact (MK_COMB (@lem73192) (@lem73191 P h1)). Qed.
Lemma lem73195 {A : Type'} (t : Prop) : (term62 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem73196 (t : Prop) : (term63 t) = t.
Proof. exact (@lem73195 ind t). Qed.
Lemma lem73197 : term61 = True.
Proof. exact (@lem73196 True). Qed.
Lemma lem73198 (P : nat -> Prop) (h1 : term42 P) : (term42 P) = True.
Proof. exact (TRANS (@lem73193 P h1) (@lem73197)). Qed.
Lemma lem73199 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem73200 (P : nat -> Prop) (h1 : term42 P) : (term46 P) = (imp True).
Proof. exact (MK_COMB (@lem73199) (@lem73198 P h1)). Qed.
Lemma lem73209 (P : nat -> Prop) : (term53 P) = (term53 P).
Proof. exact (eq_refl (term53 P)). Qed.
Lemma lem73210 (P : nat -> Prop) (h1 : term42 P) : (term54 P) = (term64 P).
Proof. exact (MK_COMB (@lem73200 P h1) (@lem73209 P)). Qed.
Lemma lem73212 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem73213 (P : nat -> Prop) : (term64 P) = (term53 P).
Proof. exact (@lem73212 (term53 P)). Qed.
Lemma lem73222 (P : nat -> Prop) (h1 : term42 P) : (term54 P) = (term53 P).
Proof. exact (TRANS (@lem73210 P h1) (@lem73213 P)). Qed.
Lemma lem73223 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem73224 (P : nat -> Prop) (h1 : term42 P) : (term56 P) = (term65 P).
Proof. exact (MK_COMB (@lem73223) (@lem73222 P h1)). Qed.
Lemma lem73225 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem73226 (n : nat) (P : nat -> Prop) (h1 : term42 P) : (term58 P n) = (term66 P n).
Proof. exact (MK_COMB (@lem73224 P h1) (@lem73225 P n)). Qed.
Lemma lem73229 (n : nat) (P : nat -> Prop) (h1 : term42 P) : (term66 P n) = (term58 P n).
Proof. exact (SYM (@lem73226 n P h1)). Qed.
Lemma lem73230 (P : nat -> Prop) (i : ind) (h1 : term19 P i) : term19 P i.
Proof. exact (h1). Qed.
Lemma lem73231 (P : nat -> Prop) (i : ind) (h1 : term67 P i) : term67 P i.
Proof. exact (h1). Qed.
Lemma lem73232 (i : ind) (h1 : NUM_REP i) : NUM_REP i.
Proof. exact (h1). Qed.
Lemma lem73234 (i : ind) : term5 i.
Proof. exact (EQ_MP (@lem72998 i) (@lem72997 i)). Qed.
Lemma lem73242 (i : ind) : (NUM_REP i) = ((NUM_REP i) = True).
Proof. exact (@lem7 (NUM_REP i)). Qed.
Lemma lem73247 (i : ind) (h1 : NUM_REP i) : (NUM_REP i) = True.
Proof. exact (EQ_MP (@lem73242 i) (@lem73232 i h1)). Qed.
Lemma lem73248 (i : ind) (h1 : NUM_REP i) : True = (NUM_REP i).
Proof. exact (SYM (@lem73247 i h1)). Qed.
Lemma lem73249 (i : ind) (h1 : NUM_REP i) : NUM_REP i.
Proof. exact (EQ_MP (@lem73248 i h1) (@lem0)). Qed.
Lemma lem73250 (i : ind) (h1 : NUM_REP i) : term6 i.
Proof. exact (@lem73234 i (@lem73249 i h1)). Qed.
Lemma lem73251 (i : ind) (h1 : (term68 i) = (term69 i)) : (term68 i) = (term69 i).
Proof. exact (h1). Qed.
Lemma lem73252 (P : nat -> Prop) : (term70 P) = (term70 P).
Proof. exact (eq_refl (term70 P)). Qed.
Lemma lem73253 (P : nat -> Prop) (i : ind) (h1 : (term68 i) = (term69 i)) : (term71 P i) = (term72 P i).
Proof. exact (MK_COMB (@lem73252 P) (@lem73251 i h1)). Qed.
Lemma lem73254 (P : nat -> Prop) (i : ind) : (term72 P i) = (term73 P i).
Proof. exact (eq_refl (term72 P i)). Qed.
Lemma lem73255 (P : nat -> Prop) (i : ind) : (term74 P i) = (term74 P i).
Proof. exact (eq_refl (term74 P i)). Qed.
Lemma lem73256 (P : nat -> Prop) (i : ind) : ((term71 P i) = (term72 P i)) = ((term71 P i) = (term73 P i)).
Proof. exact (MK_COMB (@lem73255 P i) (@lem73254 P i)). Qed.
Lemma lem73257 (P : nat -> Prop) (i : ind) : (term71 P i) = (term75 P i).
Proof. exact (eq_refl (term71 P i)). Qed.
Lemma lem73258 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem73259 (P : nat -> Prop) (i : ind) : (term74 P i) = (term76 P i).
Proof. exact (MK_COMB (@lem73258) (@lem73257 P i)). Qed.
Lemma lem73260 (P : nat -> Prop) (i : ind) : (term73 P i) = (term73 P i).
Proof. exact (eq_refl (term73 P i)). Qed.
Lemma lem73261 (P : nat -> Prop) (i : ind) : ((term71 P i) = (term73 P i)) = ((term75 P i) = (term73 P i)).
Proof. exact (MK_COMB (@lem73259 P i) (@lem73260 P i)). Qed.
Lemma lem73262 (P : nat -> Prop) (i : ind) : ((term71 P i) = (term72 P i)) = ((term75 P i) = (term73 P i)).
Proof. exact (TRANS (@lem73256 P i) (@lem73261 P i)). Qed.
Lemma lem73263 (P : nat -> Prop) (i : ind) (h1 : (term68 i) = (term69 i)) : (term75 P i) = (term73 P i).
Proof. exact (EQ_MP (@lem73262 P i) (@lem73253 P i h1)). Qed.
Lemma lem73264 (P : nat -> Prop) (i : ind) (h1 : (term68 i) = (term69 i)) : (term73 P i) = (term75 P i).
Proof. exact (SYM (@lem73263 P i h1)). Qed.
Lemma lem73268 (n : nat) : (S n) = (term2 n).
Proof. exact (EQ_MP (@lem72981 n) (@lem72980 n)). Qed.
Lemma lem73269 (i : ind) : (term69 i) = (term77 i).
Proof. exact (@lem73268 (mk_num i)). Qed.
Lemma lem73270 (i : ind) : (term78 i) = (term78 i).
Proof. exact (eq_refl (term78 i)). Qed.
Lemma lem73271 (i : ind) : ((term68 i) = (term69 i)) = ((term68 i) = (term77 i)).
Proof. exact (MK_COMB (@lem73270 i) (@lem73269 i)). Qed.
Lemma lem73274 (i : ind) : ((term68 i) = (term77 i)) = ((term68 i) = (term69 i)).
Proof. exact (SYM (@lem73271 i)). Qed.
Lemma lem73275 : mk_num = mk_num.
Proof. exact (eq_refl mk_num). Qed.
Lemma lem73276 : IND_SUC = IND_SUC.
Proof. exact (eq_refl IND_SUC). Qed.
Lemma lem73277 (i : ind) (h1 : i = (term0 i)) : i = (term0 i).
Proof. exact (h1). Qed.
Lemma lem73278 (i : ind) (h1 : i = (term0 i)) : (term0 i) = i.
Proof. exact (SYM (@lem73277 i h1)). Qed.
Lemma lem73279 (i : ind) (h1 : (term0 i) = i) : (term0 i) = i.
Proof. exact (h1). Qed.
Lemma lem73280 (i : ind) (h1 : (term0 i) = i) : i = (term0 i).
Proof. exact (SYM (@lem73279 i h1)). Qed.
Lemma lem73281 (i : ind) : (i = (term0 i)) = ((term0 i) = i).
Proof. exact (prop_ext (fun h1 : i = (term0 i) => @lem73278 i h1) (fun h1 : (term0 i) = i => @lem73280 i h1)). Qed.
Lemma lem73282 (i : ind) : ((term0 i) = i) = (i = (term0 i)).
Proof. exact (SYM (@lem73281 i)). Qed.
Lemma lem73284 (r : ind) : ((term0 r) = r) = (NUM_REP r).
Proof. exact (EQ_MP (@lem72978 r) (@lem71261 r)). Qed.
Lemma lem73285 (i : ind) : ((term0 i) = i) = (NUM_REP i).
Proof. exact (@lem73284 i). Qed.
Lemma lem73286 (i : ind) : (NUM_REP i) = ((term0 i) = i).
Proof. exact (SYM (@lem73285 i)). Qed.
Lemma lem73290 (i : ind) (h1 : NUM_REP i) : NUM_REP i.
Proof. exact (h1). Qed.
Lemma lem73291 (i : ind) (h1 : NUM_REP i) : (term0 i) = i.
Proof. exact (EQ_MP (@lem73286 i) (@lem73290 i h1)). Qed.
Lemma lem73292 (i : ind) (h1 : NUM_REP i) : i = (term0 i).
Proof. exact (EQ_MP (@lem73282 i) (@lem73291 i h1)). Qed.
Lemma lem73293 (i : ind) (h1 : NUM_REP i) : (IND_SUC i) = (term79 i).
Proof. exact (MK_COMB (@lem73276) (@lem73292 i h1)). Qed.
Lemma lem73294 (i : ind) (h1 : NUM_REP i) : (term68 i) = (term77 i).
Proof. exact (MK_COMB (@lem73275) (@lem73293 i h1)). Qed.
Lemma lem73295 (i : ind) (h1 : NUM_REP i) : (term68 i) = (term69 i).
Proof. exact (EQ_MP (@lem73274 i) (@lem73294 i h1)). Qed.
Lemma lem73296 (P : nat -> Prop) (h1 : term13 P) : term13 P.
Proof. exact (h1). Qed.
Lemma lem73297 (n : nat) (P : nat -> Prop) (h1 : term13 P) : term80 P n.
Proof. exact (@lem73296 P h1 n). Qed.
Lemma lem73298 (P : nat -> Prop) (n : nat) : (term80 P n) = (term81 P n).
Proof. exact (eq_refl (term80 P n)). Qed.
Lemma lem73299 (n : nat) (P : nat -> Prop) (h1 : term13 P) : term81 P n.
Proof. exact (EQ_MP (@lem73298 P n) (@lem73297 n P h1)). Qed.
Lemma lem73300 (P : nat -> Prop) (n : nat) (h1 : P n) : P n.
Proof. exact (h1). Qed.
Lemma lem73301 (P : nat -> Prop) (n : nat) (h1 : term13 P) (h2 : P n) : term82 P n.
Proof. exact (@lem73299 n P h1 (@lem73300 P n h2)). Qed.
Lemma lem73302 (P : nat -> Prop) (n : nat) (h1 : P n) : term83 P n.
Proof. exact (fun h0 : term13 P => @lem73301 P n h0 h1). Qed.
Lemma lem73303 (P : nat -> Prop) (h1 : term13 P) : term13 P.
Proof. exact (h1). Qed.
Lemma lem73304 (P : nat -> Prop) (n : nat) (h1 : term13 P) (h2 : P n) : term82 P n.
Proof. exact (@lem73302 P n h2 (@lem73303 P h1)). Qed.
Lemma lem73305 (n : nat) (P : nat -> Prop) (h1 : term13 P) : term81 P n.
Proof. exact (fun h0 : P n => @lem73304 P n h1 h0). Qed.
Lemma lem73306 (P : nat -> Prop) (h1 : term13 P) : term13 P.
Proof. exact (fun n : nat => @lem73305 n P h1). Qed.
Lemma lem73307 (P : nat -> Prop) : term84 P.
Proof. exact (fun h0 : term13 P => @lem73306 P h0). Qed.
Lemma lem73308 (P : nat -> Prop) (h1 : term13 P) : term13 P.
Proof. exact (@lem73307 P (@lem73010 P h1)). Qed.
Lemma lem73309 (n : nat) (P : nat -> Prop) (h1 : term13 P) : term80 P n.
Proof. exact (@lem73308 P h1 n). Qed.
Lemma lem73310 (P : nat -> Prop) (n : nat) : (term80 P n) = (term81 P n).
Proof. exact (eq_refl (term80 P n)). Qed.
Lemma lem73313 (n : nat) (P : nat -> Prop) (h1 : term13 P) : term81 P n.
Proof. exact (EQ_MP (@lem73310 P n) (@lem73309 n P h1)). Qed.
Lemma lem73314 (i : ind) (P : nat -> Prop) (h1 : term13 P) : term85 P i.
Proof. exact (@lem73313 (mk_num i) P h1). Qed.
Lemma lem73316 (P : nat -> Prop) (i : ind) (h1 : term67 P i) : term67 P i.
Proof. exact (h1). Qed.
Lemma lem73317 (P : nat -> Prop) (i : ind) (h1 : term13 P) (h2 : term67 P i) : term73 P i.
Proof. exact (@lem73314 i P h1 (@lem73316 P i h2)). Qed.
Lemma lem73318 (P : nat -> Prop) (i : ind) (h1 : term13 P) (h2 : term67 P i) (h3 : (term68 i) = (term69 i)) : term75 P i.
Proof. exact (EQ_MP (@lem73264 P i h3) (@lem73317 P i h1 h2)). Qed.
Lemma lem73319 (P : nat -> Prop) (i : ind) (h1 : term13 P) (h2 : NUM_REP i) (h3 : term67 P i) : ((term68 i) = (term69 i)) = (term75 P i).
Proof. exact (prop_ext (fun h4 : (term68 i) = (term69 i) => @lem73318 P i h1 h3 h4) (fun h4 : term75 P i => @lem73295 i h2)). Qed.
Lemma lem73320 (P : nat -> Prop) (i : ind) (h1 : term13 P) (h2 : NUM_REP i) (h3 : term67 P i) : term75 P i.
Proof. exact (EQ_MP (@lem73319 P i h1 h2 h3) (@lem73295 i h2)). Qed.
Lemma lem73321 (P : nat -> Prop) (i : ind) (h1 : term13 P) (h2 : NUM_REP i) (h3 : term67 P i) : term36 P i.
Proof. exact (conj (@lem73250 i h2) (@lem73320 P i h1 h2 h3)). Qed.
Lemma lem73322 (P : nat -> Prop) (i : ind) (h1 : term19 P i) : term67 P i.
Proof. exact (proj2 (@lem73230 P i h1)). Qed.
Lemma lem73323 (P : nat -> Prop) (i : ind) (h1 : term19 P i) : NUM_REP i.
Proof. exact (proj1 (@lem73230 P i h1)). Qed.
Lemma lem73324 (P : nat -> Prop) (i : ind) (h1 : term13 P) (h2 : NUM_REP i) (h3 : term67 P i) : (term67 P i) = (term36 P i).
Proof. exact (prop_ext (fun h4 : term67 P i => @lem73321 P i h1 h2 h3) (fun h4 : term36 P i => @lem73231 P i h3)). Qed.
Lemma lem73325 (P : nat -> Prop) (i : ind) (h1 : term13 P) (h2 : NUM_REP i) (h3 : term67 P i) : term36 P i.
Proof. exact (EQ_MP (@lem73324 P i h1 h2 h3) (@lem73231 P i h3)). Qed.
Lemma lem73326 (P : nat -> Prop) (i : ind) (h1 : term13 P) (h2 : NUM_REP i) (h3 : term67 P i) : (NUM_REP i) = (term36 P i).
Proof. exact (prop_ext (fun h4 : NUM_REP i => @lem73325 P i h1 h2 h3) (fun h4 : term36 P i => @lem73232 i h2)). Qed.
Lemma lem73327 (P : nat -> Prop) (i : ind) (h1 : term13 P) (h2 : NUM_REP i) (h3 : term67 P i) : term36 P i.
Proof. exact (EQ_MP (@lem73326 P i h1 h2 h3) (@lem73232 i h2)). Qed.
Lemma lem73328 (P : nat -> Prop) (i : ind) (h1 : term13 P) (h2 : NUM_REP i) (h3 : term19 P i) : (term67 P i) = (term36 P i).
Proof. exact (prop_ext (fun h4 : term67 P i => @lem73327 P i h1 h2 h4) (fun h4 : term36 P i => @lem73322 P i h3)). Qed.
Lemma lem73329 (P : nat -> Prop) (i : ind) (h1 : term13 P) (h2 : NUM_REP i) (h3 : term19 P i) : term36 P i.
Proof. exact (EQ_MP (@lem73328 P i h1 h2 h3) (@lem73322 P i h3)). Qed.
Lemma lem73330 (P : nat -> Prop) (i : ind) (h1 : term13 P) (h2 : term19 P i) : (NUM_REP i) = (term36 P i).
Proof. exact (prop_ext (fun h3 : NUM_REP i => @lem73329 P i h1 h3 h2) (fun h3 : term36 P i => @lem73323 P i h2)). Qed.
Lemma lem73331 (P : nat -> Prop) (i : ind) (h1 : term13 P) (h2 : term19 P i) : term36 P i.
Proof. exact (EQ_MP (@lem73330 P i h1 h2) (@lem73323 P i h2)). Qed.
Lemma lem73332 (i : ind) (P : nat -> Prop) (h1 : term13 P) : term38 P i.
Proof. exact (fun h0 : term19 P i => @lem73331 P i h1 h0). Qed.
Lemma lem73337 (P : nat -> Prop) (h1 : term13 P) : term42 P.
Proof. exact (fun i : ind => @lem73332 i P h1). Qed.
Lemma lem73338 (P : nat -> Prop) (h1 : term53 P) : term53 P.
Proof. exact (h1). Qed.
Lemma lem73339 (n : nat) (P : nat -> Prop) (h1 : term53 P) : term86 P n.
Proof. exact (@lem73338 P h1 (dest_num n)). Qed.
Lemma lem73340 (P : nat -> Prop) (n : nat) : (term86 P n) = (term87 P n).
Proof. exact (eq_refl (term86 P n)). Qed.
Lemma lem73341 (n : nat) (P : nat -> Prop) (h1 : term53 P) : term87 P n.
Proof. exact (EQ_MP (@lem73340 P n) (@lem73339 n P h1)). Qed.
Lemma lem73347 (r : ind) : (NUM_REP r) = ((term0 r) = r).
Proof. exact (@axiom_8 r). Qed.
Lemma lem73348 (n : nat) : (term88 n) = ((term89 n) = (dest_num n)).
Proof. exact (@lem73347 (dest_num n)). Qed.
Lemma lem73352 (a : nat) : (term90 a) = a.
Proof. exact (@axiom_7 a). Qed.
Lemma lem73353 (n : nat) : (term90 n) = n.
Proof. exact (@lem73352 n). Qed.
Lemma lem73354 : dest_num = dest_num.
Proof. exact (eq_refl dest_num). Qed.
Lemma lem73355 (n : nat) : (term89 n) = (dest_num n).
Proof. exact (MK_COMB (@lem73354) (@lem73353 n)). Qed.
Lemma lem73356 : (@eq ind) = (@eq ind).
Proof. exact (eq_refl (@eq ind)). Qed.
Lemma lem73357 (n : nat) : (term91 n) = (term92 n).
Proof. exact (MK_COMB (@lem73356) (@lem73355 n)). Qed.
Lemma lem73358 (n : nat) : (dest_num n) = (dest_num n).
Proof. exact (eq_refl (dest_num n)). Qed.
Lemma lem73359 (n : nat) : ((term89 n) = (dest_num n)) = ((dest_num n) = (dest_num n)).
Proof. exact (MK_COMB (@lem73357 n) (@lem73358 n)). Qed.
Lemma lem73361 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem73362 (x : ind) : (x = x) = True.
Proof. exact (@lem73361 ind x). Qed.
Lemma lem73363 (n : nat) : ((dest_num n) = (dest_num n)) = True.
Proof. exact (@lem73362 (dest_num n)). Qed.
Lemma lem73364 (n : nat) : ((term89 n) = (dest_num n)) = True.
Proof. exact (TRANS (@lem73359 n) (@lem73363 n)). Qed.
Lemma lem73365 (n : nat) : (term88 n) = True.
Proof. exact (TRANS (@lem73348 n) (@lem73364 n)). Qed.
Lemma lem73366 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem73367 (n : nat) : (term93 n) = (imp True).
Proof. exact (MK_COMB (@lem73366) (@lem73365 n)). Qed.
Lemma lem73371 (r : ind) : (NUM_REP r) = ((term0 r) = r).
Proof. exact (@axiom_8 r). Qed.
Lemma lem73372 (n : nat) : (term88 n) = ((term89 n) = (dest_num n)).
Proof. exact (@lem73371 (dest_num n)). Qed.
Lemma lem73376 (a : nat) : (term90 a) = a.
Proof. exact (@axiom_7 a). Qed.
Lemma lem73377 (n : nat) : (term90 n) = n.
Proof. exact (@lem73376 n). Qed.
Lemma lem73378 : dest_num = dest_num.
Proof. exact (eq_refl dest_num). Qed.
Lemma lem73379 (n : nat) : (term89 n) = (dest_num n).
Proof. exact (MK_COMB (@lem73378) (@lem73377 n)). Qed.
Lemma lem73380 : (@eq ind) = (@eq ind).
Proof. exact (eq_refl (@eq ind)). Qed.
Lemma lem73381 (n : nat) : (term91 n) = (term92 n).
Proof. exact (MK_COMB (@lem73380) (@lem73379 n)). Qed.
Lemma lem73382 (n : nat) : (dest_num n) = (dest_num n).
Proof. exact (eq_refl (dest_num n)). Qed.
Lemma lem73383 (n : nat) : ((term89 n) = (dest_num n)) = ((dest_num n) = (dest_num n)).
Proof. exact (MK_COMB (@lem73381 n) (@lem73382 n)). Qed.
Lemma lem73385 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem73386 (x : ind) : (x = x) = True.
Proof. exact (@lem73385 ind x). Qed.
Lemma lem73387 (n : nat) : ((dest_num n) = (dest_num n)) = True.
Proof. exact (@lem73386 (dest_num n)). Qed.
Lemma lem73388 (n : nat) : ((term89 n) = (dest_num n)) = True.
Proof. exact (TRANS (@lem73383 n) (@lem73387 n)). Qed.
Lemma lem73389 (n : nat) : (term88 n) = True.
Proof. exact (TRANS (@lem73372 n) (@lem73388 n)). Qed.
Lemma lem73390 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem73391 (n : nat) : (term94 n) = (and True).
Proof. exact (MK_COMB (@lem73390) (@lem73389 n)). Qed.
Lemma lem73393 (a : nat) : (term90 a) = a.
Proof. exact (@axiom_7 a). Qed.
Lemma lem73394 (n : nat) : (term90 n) = n.
Proof. exact (@lem73393 n). Qed.
Lemma lem73395 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem73396 (P : nat -> Prop) (n : nat) : (term95 P n) = (P n).
Proof. exact (MK_COMB (@lem73395 P) (@lem73394 n)). Qed.
Lemma lem73397 (P : nat -> Prop) (n : nat) : (term96 P n) = (term97 P n).
Proof. exact (MK_COMB (@lem73391 n) (@lem73396 P n)). Qed.
Lemma lem73399 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem73400 (P : nat -> Prop) (n : nat) : (term97 P n) = (P n).
Proof. exact (@lem73399 (P n)). Qed.
Lemma lem73401 (P : nat -> Prop) (n : nat) : (term96 P n) = (P n).
Proof. exact (TRANS (@lem73397 P n) (@lem73400 P n)). Qed.
Lemma lem73402 (P : nat -> Prop) (n : nat) : (term87 P n) = (term98 P n).
Proof. exact (MK_COMB (@lem73367 n) (@lem73401 P n)). Qed.
Lemma lem73404 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem73405 (P : nat -> Prop) (n : nat) : (term98 P n) = (P n).
Proof. exact (@lem73404 (P n)). Qed.
Lemma lem73406 (P : nat -> Prop) (n : nat) : (term87 P n) = (P n).
Proof. exact (TRANS (@lem73402 P n) (@lem73405 P n)). Qed.
Lemma lem73407 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem73408 (P : nat -> Prop) (n : nat) : (term99 P n) = (term100 P n).
Proof. exact (MK_COMB (@lem73407) (@lem73406 P n)). Qed.
Lemma lem73409 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem73410 (P : nat -> Prop) (n : nat) : (term101 P n) = (term102 P n).
Proof. exact (MK_COMB (@lem73408 P n) (@lem73409 P n)). Qed.
Lemma lem73412 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem73413 (P : nat -> Prop) (n : nat) : (term102 P n) = True.
Proof. exact (@lem73412 (P n)). Qed.
Lemma lem73414 (P : nat -> Prop) (n : nat) : (term101 P n) = True.
Proof. exact (TRANS (@lem73410 P n) (@lem73413 P n)). Qed.
Lemma lem73415 (P : nat -> Prop) (n : nat) : True = (term101 P n).
Proof. exact (SYM (@lem73414 P n)). Qed.
Lemma lem73416 (P : nat -> Prop) (n : nat) : term101 P n.
Proof. exact (EQ_MP (@lem73415 P n) (@lem0)). Qed.
Lemma lem73417 (n : nat) (P : nat -> Prop) (h1 : term53 P) : P n.
Proof. exact (@lem73416 P n (@lem73341 n P h1)). Qed.
Lemma lem73418 (P : nat -> Prop) (n : nat) : term66 P n.
Proof. exact (fun h0 : term53 P => @lem73417 n P h0). Qed.
Lemma lem73419 (n : nat) (P : nat -> Prop) (h1 : term42 P) : term58 P n.
Proof. exact (EQ_MP (@lem73229 n P h1) (@lem73418 P n)). Qed.
Lemma lem73420 (n : nat) (P : nat -> Prop) (h1 : term13 P) : (term42 P) = (term58 P n).
Proof. exact (prop_ext (fun h2 : term42 P => @lem73419 n P h2) (fun h2 : term58 P n => @lem73337 P h1)). Qed.
Lemma lem73421 (n : nat) (P : nat -> Prop) (h1 : term13 P) : term58 P n.
Proof. exact (EQ_MP (@lem73420 n P h1) (@lem73337 P h1)). Qed.
Lemma lem73422 (n : nat) (P : nat -> Prop) (h1 : term13 P) (h2 : P 0) : term57 P n.
Proof. exact (EQ_MP (@lem73174 n P h2) (@lem73421 n P h1)). Qed.
Lemma lem73423 (n : nat) (P : nat -> Prop) (h1 : term13 P) (h2 : P 0) : P n.
Proof. exact (@lem73422 n P h1 h2 (@lem73008 P)). Qed.
Lemma lem73428 (P : nat -> Prop) (h1 : term13 P) (h2 : P 0) : term103 P.
Proof. exact (fun n : nat => @lem73423 n P h1 h2). Qed.
Lemma lem73429 (P : nat -> Prop) (h1 : term12 P) : term13 P.
Proof. exact (proj2 (@lem73009 P h1)). Qed.
Lemma lem73430 (P : nat -> Prop) (h1 : term12 P) : P 0.
Proof. exact (proj1 (@lem73009 P h1)). Qed.
Lemma lem73431 (P : nat -> Prop) (h1 : term13 P) (h2 : P 0) : (term13 P) = (term103 P).
Proof. exact (prop_ext (fun h3 : term13 P => @lem73428 P h1 h2) (fun h3 : term103 P => @lem73010 P h1)). Qed.
Lemma lem73432 (P : nat -> Prop) (h1 : term13 P) (h2 : P 0) : term103 P.
Proof. exact (EQ_MP (@lem73431 P h1 h2) (@lem73010 P h1)). Qed.
Lemma lem73433 (P : nat -> Prop) (h1 : term13 P) (h2 : P 0) : (P 0) = (term103 P).
Proof. exact (prop_ext (fun h3 : P 0 => @lem73432 P h1 h2) (fun h3 : term103 P => @lem73011 P h2)). Qed.
Lemma lem73434 (P : nat -> Prop) (h1 : term13 P) (h2 : P 0) : term103 P.
Proof. exact (EQ_MP (@lem73433 P h1 h2) (@lem73011 P h2)). Qed.
Lemma lem73435 (P : nat -> Prop) (h1 : P 0) (h2 : term12 P) : (term13 P) = (term103 P).
Proof. exact (prop_ext (fun h3 : term13 P => @lem73434 P h3 h1) (fun h3 : term103 P => @lem73429 P h2)). Qed.
Lemma lem73436 (P : nat -> Prop) (h1 : P 0) (h2 : term12 P) : term103 P.
Proof. exact (EQ_MP (@lem73435 P h1 h2) (@lem73429 P h2)). Qed.
Lemma lem73437 (P : nat -> Prop) (h1 : term12 P) : (P 0) = (term103 P).
Proof. exact (prop_ext (fun h2 : P 0 => @lem73436 P h2 h1) (fun h2 : term103 P => @lem73430 P h1)). Qed.
Lemma lem73438 (P : nat -> Prop) (h1 : term12 P) : term103 P.
Proof. exact (EQ_MP (@lem73437 P h1) (@lem73430 P h1)). Qed.
Lemma lem73439 (P : nat -> Prop) : term104 P.
Proof. exact (fun h0 : term12 P => @lem73438 P h0). Qed.
Lemma lem73444 : term105.
Proof. exact (fun P : nat -> Prop => @lem73439 P). Qed.
