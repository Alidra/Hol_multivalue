Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483205_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import real_ge_spec.
Require Import real_gt_spec.
Require Import real_lt_spec.
Require Import real_max_spec.
Require Import thm0_spec.
Require Import thm13473_spec.
Require Import thm1833_spec.
Require Import thm1834_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem1482982 (y : real) : term0 y.
Proof. exact (@lem1342163 y). Qed.
Lemma lem1482983 (y : real) : (term0 y) = (term1 y).
Proof. exact (eq_refl (term0 y)). Qed.
Lemma lem1482984 (y : real) : term1 y.
Proof. exact (EQ_MP (@lem1482983 y) (@lem1482982 y)). Qed.
Lemma lem1482985 (y : real) (x : real) : term2 y x.
Proof. exact (@lem1482984 y x). Qed.
Lemma lem1482986 (y : real) (x : real) : (term2 y x) = ((real_ge x y) = (real_le y x)).
Proof. exact (eq_refl (term2 y x)). Qed.
Lemma lem1482988 (y : real) : term3 y.
Proof. exact (@lem1342768 y). Qed.
Lemma lem1482989 (y : real) : (term3 y) = (term4 y).
Proof. exact (eq_refl (term3 y)). Qed.
Lemma lem1482990 (y : real) : term4 y.
Proof. exact (EQ_MP (@lem1482989 y) (@lem1482988 y)). Qed.
Lemma lem1482991 (y : real) (x : real) : term5 y x.
Proof. exact (@lem1482990 y x). Qed.
Lemma lem1482992 (y : real) (x : real) : (term5 y x) = ((real_gt x y) = (real_lt y x)).
Proof. exact (eq_refl (term5 y x)). Qed.
Lemma lem1482994 (n : real) : term6 n.
Proof. exact (@lem1345564 n). Qed.
Lemma lem1482995 (n : real) : (term6 n) = (term7 n).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem1482996 (n : real) : term7 n.
Proof. exact (EQ_MP (@lem1482995 n) (@lem1482994 n)). Qed.
Lemma lem1482997 (n : real) (m : real) : term8 n m.
Proof. exact (@lem1482996 n m). Qed.
Lemma lem1482998 (n : real) (m : real) : (term8 n m) = ((real_max m n) = (term9 n m)).
Proof. exact (eq_refl (term8 n m)). Qed.
Lemma lem1483003 (n : real) (m : real) : (real_max m n) = (term9 n m).
Proof. exact (EQ_MP (@lem1482998 n m) (@lem1482997 n m)). Qed.
Lemma lem1483004 (y : real) (x : real) : (real_max x y) = (term9 y x).
Proof. exact (@lem1483003 y x). Qed.
Lemma lem1483005 (P : real -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1483006 (P : real -> Prop) (y : real) (x : real) : (term10 P x y) = (term11 P y x).
Proof. exact (MK_COMB (@lem1483005 P) (@lem1483004 y x)). Qed.
Lemma lem1483007 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1483008 (P : real -> Prop) (y : real) (x : real) : (term12 P x y) = (term13 P y x).
Proof. exact (MK_COMB (@lem1483007) (@lem1483006 P y x)). Qed.
Lemma lem1483014 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1482986 y x) (@lem1482985 y x)). Qed.
Lemma lem1483015 (x : real) (y : real) : (real_ge y x) = (real_le x y).
Proof. exact (@lem1483014 x y). Qed.
Lemma lem1483016 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1483017 (x : real) (y : real) : (term14 y x) = (term15 x y).
Proof. exact (MK_COMB (@lem1483016) (@lem1483015 x y)). Qed.
Lemma lem1483018 (P : real -> Prop) (y : real) : (P y) = (P y).
Proof. exact (eq_refl (P y)). Qed.
Lemma lem1483019 (x : real) (P : real -> Prop) (y : real) : (term16 x P y) = (term17 x P y).
Proof. exact (MK_COMB (@lem1483017 x y) (@lem1483018 P y)). Qed.
Lemma lem1483022 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1483023 (x : real) (P : real -> Prop) (y : real) : (term18 x P y) = (term19 x P y).
Proof. exact (MK_COMB (@lem1483022) (@lem1483019 x P y)). Qed.
Lemma lem1483027 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1482992 y x) (@lem1482991 y x)). Qed.
Lemma lem1483028 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1483029 (y : real) (x : real) : (term20 x y) = (term21 y x).
Proof. exact (MK_COMB (@lem1483028) (@lem1483027 y x)). Qed.
Lemma lem1483030 (P : real -> Prop) (x : real) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1483031 (y : real) (P : real -> Prop) (x : real) : (term22 y P x) = (term23 y P x).
Proof. exact (MK_COMB (@lem1483029 y x) (@lem1483030 P x)). Qed.
Lemma lem1483034 (y : real) (P : real -> Prop) (x : real) : (term24 y P x) = (term25 y P x).
Proof. exact (MK_COMB (@lem1483023 x P y) (@lem1483031 y P x)). Qed.
Lemma lem1483037 (y : real) (P : real -> Prop) (x : real) : ((term10 P x y) = (term24 y P x)) = ((term11 P y x) = (term25 y P x)).
Proof. exact (MK_COMB (@lem1483008 P y x) (@lem1483034 y P x)). Qed.
Lemma lem1483040 (y : real) (P : real -> Prop) (x : real) : ((term11 P y x) = (term25 y P x)) = ((term10 P x y) = (term24 y P x)).
Proof. exact (SYM (@lem1483037 y P x)). Qed.
Lemma lem1483041 (_474 : real) (_475 : Prop) (_476 : real -> Prop) (_477 : real) : (term26 _476 _475 _474 _477) = (term27 _474 _475 _476 _477).
Proof. exact (@lem13473 real _474 _475 _476 _477). Qed.
Lemma lem1483042 (_474 : real) (_475 : Prop) (y : real) (P : real -> Prop) (x : real) (_477 : real) : (term28 y P x _475 _474 _477) = (term29 _474 _475 y P x _477).
Proof. exact (@lem1483041 _474 _475 (term30 y P x) _477). Qed.
Lemma lem1483043 (y : real) (P : real -> Prop) (x : real) : (term31 P y x) = (term32 y P x).
Proof. exact (@lem1483042 y (real_le x y) y P x x). Qed.
Lemma lem1483044 (y : real) (P : real -> Prop) (x : real) : (term33 y P x) = ((P x) = (term25 y P x)).
Proof. exact (eq_refl (term33 y P x)). Qed.
Lemma lem1483045 (x : real) (y : real) : (term34 x y) = (term34 x y).
Proof. exact (eq_refl (term34 x y)). Qed.
Lemma lem1483046 (y : real) (P : real -> Prop) (x : real) : (term35 y P x) = (term36 y P x).
Proof. exact (MK_COMB (@lem1483045 x y) (@lem1483044 y P x)). Qed.
Lemma lem1483047 (y : real) (P : real -> Prop) (x : real) : (term37 P x y) = ((P y) = (term25 y P x)).
Proof. exact (eq_refl (term37 P x y)). Qed.
Lemma lem1483048 (x : real) (y : real) : (term38 x y) = (term38 x y).
Proof. exact (eq_refl (term38 x y)). Qed.
Lemma lem1483049 (y : real) (P : real -> Prop) (x : real) : (term39 P x y) = (term40 y P x).
Proof. exact (MK_COMB (@lem1483048 x y) (@lem1483047 y P x)). Qed.
Lemma lem1483050 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1483051 (y : real) (P : real -> Prop) (x : real) : (term41 P x y) = (term42 y P x).
Proof. exact (MK_COMB (@lem1483050) (@lem1483049 y P x)). Qed.
Lemma lem1483052 (y : real) (P : real -> Prop) (x : real) : (term32 y P x) = (term43 y P x).
Proof. exact (MK_COMB (@lem1483051 y P x) (@lem1483046 y P x)). Qed.
Lemma lem1483053 (y : real) (P : real -> Prop) (x : real) : (term31 P y x) = ((term11 P y x) = (term25 y P x)).
Proof. exact (eq_refl (term31 P y x)). Qed.
Lemma lem1483054 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1483055 (y : real) (P : real -> Prop) (x : real) : (term44 P y x) = (term45 y P x).
Proof. exact (MK_COMB (@lem1483054) (@lem1483053 y P x)). Qed.
Lemma lem1483056 (y : real) (P : real -> Prop) (x : real) : ((term31 P y x) = (term32 y P x)) = (((term11 P y x) = (term25 y P x)) = (term43 y P x)).
Proof. exact (MK_COMB (@lem1483055 y P x) (@lem1483052 y P x)). Qed.
Lemma lem1483057 (y : real) (P : real -> Prop) (x : real) : ((term11 P y x) = (term25 y P x)) = (term43 y P x).
Proof. exact (EQ_MP (@lem1483056 y P x) (@lem1483043 y P x)). Qed.
Lemma lem1483058 (y : real) (P : real -> Prop) (x : real) : (term43 y P x) = ((term11 P y x) = (term25 y P x)).
Proof. exact (SYM (@lem1483057 y P x)). Qed.
Lemma lem1483059 (x : real) (y : real) (h1 : real_le x y) : real_le x y.
Proof. exact (h1). Qed.
Lemma lem1483060 (x : real) (y : real) : (real_le x y) = ((real_le x y) = True).
Proof. exact (@lem7 (real_le x y)). Qed.
Lemma lem1483061 (x : real) (y : real) (h1 : real_le x y) : (real_le x y) = True.
Proof. exact (EQ_MP (@lem1483060 x y) (@lem1483059 x y h1)). Qed.
Lemma lem1483062 (y : real) (P : real -> Prop) (x : real) : (term46 y P x) = (term46 y P x).
Proof. exact (eq_refl (term46 y P x)). Qed.
Lemma lem1483063 (P : real -> Prop) (x : real) (y : real) (h1 : real_le x y) : (term47 P x y) = (term48 y P x).
Proof. exact (MK_COMB (@lem1483062 y P x) (@lem1483061 x y h1)). Qed.
Lemma lem1483064 (y : real) (P : real -> Prop) (x : real) : (term48 y P x) = ((P y) = (term49 y P x)).
Proof. exact (eq_refl (term48 y P x)). Qed.
Lemma lem1483065 (P : real -> Prop) (x : real) (y : real) : (term50 P x y) = (term50 P x y).
Proof. exact (eq_refl (term50 P x y)). Qed.
Lemma lem1483066 (y : real) (P : real -> Prop) (x : real) : ((term47 P x y) = (term48 y P x)) = ((term47 P x y) = ((P y) = (term49 y P x))).
Proof. exact (MK_COMB (@lem1483065 P x y) (@lem1483064 y P x)). Qed.
Lemma lem1483067 (y : real) (P : real -> Prop) (x : real) : (term47 P x y) = ((P y) = (term25 y P x)).
Proof. exact (eq_refl (term47 P x y)). Qed.
Lemma lem1483068 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1483069 (y : real) (P : real -> Prop) (x : real) : (term50 P x y) = (term51 y P x).
Proof. exact (MK_COMB (@lem1483068) (@lem1483067 y P x)). Qed.
Lemma lem1483070 (y : real) (P : real -> Prop) (x : real) : ((P y) = (term49 y P x)) = ((P y) = (term49 y P x)).
Proof. exact (eq_refl ((P y) = (term49 y P x))). Qed.
Lemma lem1483071 (y : real) (P : real -> Prop) (x : real) : ((term47 P x y) = ((P y) = (term49 y P x))) = (((P y) = (term25 y P x)) = ((P y) = (term49 y P x))).
Proof. exact (MK_COMB (@lem1483069 y P x) (@lem1483070 y P x)). Qed.
Lemma lem1483072 (y : real) (P : real -> Prop) (x : real) : ((term47 P x y) = (term48 y P x)) = (((P y) = (term25 y P x)) = ((P y) = (term49 y P x))).
Proof. exact (TRANS (@lem1483066 y P x) (@lem1483071 y P x)). Qed.
Lemma lem1483073 (P : real -> Prop) (x : real) (y : real) (h1 : real_le x y) : ((P y) = (term25 y P x)) = ((P y) = (term49 y P x)).
Proof. exact (EQ_MP (@lem1483072 y P x) (@lem1483063 P x y h1)). Qed.
Lemma lem1483074 (P : real -> Prop) (x : real) (y : real) (h1 : real_le x y) : ((P y) = (term49 y P x)) = ((P y) = (term25 y P x)).
Proof. exact (SYM (@lem1483073 P x y h1)). Qed.
Lemma lem1483075 (x : real) (y : real) (h1 : term52 x y) : term52 x y.
Proof. exact (h1). Qed.
Lemma lem1483076 (x : real) (y : real) : term53 x y.
Proof. exact (@lem82 (real_le x y)). Qed.
Lemma lem1483077 (x : real) (y : real) (h1 : term52 x y) : (real_le x y) = False.
Proof. exact (@lem1483076 x y (@lem1483075 x y h1)). Qed.
Lemma lem1483078 (y : real) (P : real -> Prop) (x : real) : (term54 y P x) = (term54 y P x).
Proof. exact (eq_refl (term54 y P x)). Qed.
Lemma lem1483079 (P : real -> Prop) (x : real) (y : real) (h1 : term52 x y) : (term55 P x y) = (term56 y P x).
Proof. exact (MK_COMB (@lem1483078 y P x) (@lem1483077 x y h1)). Qed.
Lemma lem1483080 (y : real) (P : real -> Prop) (x : real) : (term56 y P x) = ((P x) = (term57 y P x)).
Proof. exact (eq_refl (term56 y P x)). Qed.
Lemma lem1483081 (P : real -> Prop) (x : real) (y : real) : (term58 P x y) = (term58 P x y).
Proof. exact (eq_refl (term58 P x y)). Qed.
Lemma lem1483082 (y : real) (P : real -> Prop) (x : real) : ((term55 P x y) = (term56 y P x)) = ((term55 P x y) = ((P x) = (term57 y P x))).
Proof. exact (MK_COMB (@lem1483081 P x y) (@lem1483080 y P x)). Qed.
Lemma lem1483083 (y : real) (P : real -> Prop) (x : real) : (term55 P x y) = ((P x) = (term25 y P x)).
Proof. exact (eq_refl (term55 P x y)). Qed.
Lemma lem1483084 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1483085 (y : real) (P : real -> Prop) (x : real) : (term58 P x y) = (term59 y P x).
Proof. exact (MK_COMB (@lem1483084) (@lem1483083 y P x)). Qed.
Lemma lem1483086 (y : real) (P : real -> Prop) (x : real) : ((P x) = (term57 y P x)) = ((P x) = (term57 y P x)).
Proof. exact (eq_refl ((P x) = (term57 y P x))). Qed.
Lemma lem1483087 (y : real) (P : real -> Prop) (x : real) : ((term55 P x y) = ((P x) = (term57 y P x))) = (((P x) = (term25 y P x)) = ((P x) = (term57 y P x))).
Proof. exact (MK_COMB (@lem1483085 y P x) (@lem1483086 y P x)). Qed.
Lemma lem1483088 (y : real) (P : real -> Prop) (x : real) : ((term55 P x y) = (term56 y P x)) = (((P x) = (term25 y P x)) = ((P x) = (term57 y P x))).
Proof. exact (TRANS (@lem1483082 y P x) (@lem1483087 y P x)). Qed.
Lemma lem1483089 (P : real -> Prop) (x : real) (y : real) (h1 : term52 x y) : ((P x) = (term25 y P x)) = ((P x) = (term57 y P x)).
Proof. exact (EQ_MP (@lem1483088 y P x) (@lem1483079 P x y h1)). Qed.
Lemma lem1483090 (P : real -> Prop) (x : real) (y : real) (h1 : term52 x y) : ((P x) = (term57 y P x)) = ((P x) = (term25 y P x)).
Proof. exact (SYM (@lem1483089 P x y h1)). Qed.
Lemma lem1483091 (y : real) : term60 y.
Proof. exact (@lem1341566 y). Qed.
Lemma lem1483092 (y : real) : (term60 y) = (term61 y).
Proof. exact (eq_refl (term60 y)). Qed.
Lemma lem1483093 (y : real) : term61 y.
Proof. exact (EQ_MP (@lem1483092 y) (@lem1483091 y)). Qed.
Lemma lem1483094 (y : real) (x : real) : term62 y x.
Proof. exact (@lem1483093 y x). Qed.
Lemma lem1483095 (y : real) (x : real) : (term62 y x) = ((real_lt x y) = (term52 y x)).
Proof. exact (eq_refl (term62 y x)). Qed.
Lemma lem1483097 (x : real) (y : real) : (real_le x y) = ((real_le x y) = True).
Proof. exact (@lem7 (real_le x y)). Qed.
Lemma lem1483104 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1483105 (P : real -> Prop) (y : real) : (term63 P y) = (P y).
Proof. exact (@lem1483104 (P y)). Qed.
Lemma lem1483106 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1483107 (P : real -> Prop) (y : real) : (term64 P y) = (term65 P y).
Proof. exact (MK_COMB (@lem1483106) (@lem1483105 P y)). Qed.
Lemma lem1483111 (y : real) (x : real) : (real_lt x y) = (term52 y x).
Proof. exact (EQ_MP (@lem1483095 y x) (@lem1483094 y x)). Qed.
Lemma lem1483112 (x : real) (y : real) : (real_lt y x) = (term52 x y).
Proof. exact (@lem1483111 x y). Qed.
Lemma lem1483114 (x : real) (y : real) (h1 : real_le x y) : (real_le x y) = True.
Proof. exact (EQ_MP (@lem1483097 x y) (@lem1483059 x y h1)). Qed.
Lemma lem1483115 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1483116 (x : real) (y : real) (h1 : real_le x y) : (term52 x y) = (~ True).
Proof. exact (MK_COMB (@lem1483115) (@lem1483114 x y h1)). Qed.
Lemma lem1483118 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1483119 (x : real) (y : real) (h1 : real_le x y) : (term52 x y) = False.
Proof. exact (TRANS (@lem1483116 x y h1) (@lem1483118)). Qed.
Lemma lem1483120 (x : real) (y : real) (h1 : real_le x y) : (real_lt y x) = False.
Proof. exact (TRANS (@lem1483112 x y) (@lem1483119 x y h1)). Qed.
Lemma lem1483121 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1483122 (x : real) (y : real) (h1 : real_le x y) : (term21 y x) = (and False).
Proof. exact (MK_COMB (@lem1483121) (@lem1483120 x y h1)). Qed.
Lemma lem1483123 (P : real -> Prop) (x : real) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1483124 (P : real -> Prop) (x : real) (y : real) (h1 : real_le x y) : (term23 y P x) = (term66 P x).
Proof. exact (MK_COMB (@lem1483122 x y h1) (@lem1483123 P x)). Qed.
Lemma lem1483126 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1483127 (P : real -> Prop) (x : real) : (term66 P x) = False.
Proof. exact (@lem1483126 (P x)). Qed.
Lemma lem1483128 (P : real -> Prop) (x : real) (y : real) (h1 : real_le x y) : (term23 y P x) = False.
Proof. exact (TRANS (@lem1483124 P x y h1) (@lem1483127 P x)). Qed.
Lemma lem1483129 (P : real -> Prop) (x : real) (y : real) (h1 : real_le x y) : (term49 y P x) = (term67 P y).
Proof. exact (MK_COMB (@lem1483107 P y) (@lem1483128 P x y h1)). Qed.
Lemma lem1483131 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem1483132 (P : real -> Prop) (y : real) : (term67 P y) = (P y).
Proof. exact (@lem1483131 (P y)). Qed.
Lemma lem1483133 (P : real -> Prop) (x : real) (y : real) (h1 : real_le x y) : (term49 y P x) = (P y).
Proof. exact (TRANS (@lem1483129 P x y h1) (@lem1483132 P y)). Qed.
Lemma lem1483134 (P : real -> Prop) (y : real) : (term68 P y) = (term68 P y).
Proof. exact (eq_refl (term68 P y)). Qed.
Lemma lem1483135 (P : real -> Prop) (x : real) (y : real) (h1 : real_le x y) : ((P y) = (term49 y P x)) = ((P y) = (P y)).
Proof. exact (MK_COMB (@lem1483134 P y) (@lem1483133 P x y h1)). Qed.
Lemma lem1483137 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1483138 (x : Prop) : (x = x) = True.
Proof. exact (@lem1483137 Prop x). Qed.
Lemma lem1483139 (P : real -> Prop) (y : real) : ((P y) = (P y)) = True.
Proof. exact (@lem1483138 (P y)). Qed.
Lemma lem1483140 (P : real -> Prop) (x : real) (y : real) (h1 : real_le x y) : ((P y) = (term49 y P x)) = True.
Proof. exact (TRANS (@lem1483135 P x y h1) (@lem1483139 P y)). Qed.
Lemma lem1483141 (P : real -> Prop) (x : real) (y : real) (h1 : real_le x y) : True = ((P y) = (term49 y P x)).
Proof. exact (SYM (@lem1483140 P x y h1)). Qed.
Lemma lem1483142 (P : real -> Prop) (x : real) (y : real) (h1 : real_le x y) : (P y) = (term49 y P x).
Proof. exact (EQ_MP (@lem1483141 P x y h1) (@lem0)). Qed.
Lemma lem1483143 (y : real) : term60 y.
Proof. exact (@lem1341566 y). Qed.
Lemma lem1483144 (y : real) : (term60 y) = (term61 y).
Proof. exact (eq_refl (term60 y)). Qed.
Lemma lem1483145 (y : real) : term61 y.
Proof. exact (EQ_MP (@lem1483144 y) (@lem1483143 y)). Qed.
Lemma lem1483146 (y : real) (x : real) : term62 y x.
Proof. exact (@lem1483145 y x). Qed.
Lemma lem1483147 (y : real) (x : real) : (term62 y x) = ((real_lt x y) = (term52 y x)).
Proof. exact (eq_refl (term62 y x)). Qed.
Lemma lem1483149 (x : real) (y : real) : term53 x y.
Proof. exact (@lem82 (real_le x y)). Qed.
Lemma lem1483156 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1483157 (P : real -> Prop) (y : real) : (term66 P y) = False.
Proof. exact (@lem1483156 (P y)). Qed.
Lemma lem1483158 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1483159 (P : real -> Prop) (y : real) : (term69 P y) = (or False).
Proof. exact (MK_COMB (@lem1483158) (@lem1483157 P y)). Qed.
Lemma lem1483163 (y : real) (x : real) : (real_lt x y) = (term52 y x).
Proof. exact (EQ_MP (@lem1483147 y x) (@lem1483146 y x)). Qed.
Lemma lem1483164 (x : real) (y : real) : (real_lt y x) = (term52 x y).
Proof. exact (@lem1483163 x y). Qed.
Lemma lem1483166 (x : real) (y : real) (h1 : term52 x y) : (real_le x y) = False.
Proof. exact (@lem1483149 x y (@lem1483075 x y h1)). Qed.
Lemma lem1483167 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1483168 (x : real) (y : real) (h1 : term52 x y) : (term52 x y) = (~ False).
Proof. exact (MK_COMB (@lem1483167) (@lem1483166 x y h1)). Qed.
Lemma lem1483170 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1483171 (x : real) (y : real) (h1 : term52 x y) : (term52 x y) = True.
Proof. exact (TRANS (@lem1483168 x y h1) (@lem1483170)). Qed.
Lemma lem1483172 (x : real) (y : real) (h1 : term52 x y) : (real_lt y x) = True.
Proof. exact (TRANS (@lem1483164 x y) (@lem1483171 x y h1)). Qed.
Lemma lem1483173 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1483174 (x : real) (y : real) (h1 : term52 x y) : (term21 y x) = (and True).
Proof. exact (MK_COMB (@lem1483173) (@lem1483172 x y h1)). Qed.
Lemma lem1483175 (P : real -> Prop) (x : real) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1483176 (P : real -> Prop) (x : real) (y : real) (h1 : term52 x y) : (term23 y P x) = (term63 P x).
Proof. exact (MK_COMB (@lem1483174 x y h1) (@lem1483175 P x)). Qed.
Lemma lem1483178 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1483179 (P : real -> Prop) (x : real) : (term63 P x) = (P x).
Proof. exact (@lem1483178 (P x)). Qed.
Lemma lem1483180 (P : real -> Prop) (x : real) (y : real) (h1 : term52 x y) : (term23 y P x) = (P x).
Proof. exact (TRANS (@lem1483176 P x y h1) (@lem1483179 P x)). Qed.
Lemma lem1483181 (P : real -> Prop) (x : real) (y : real) (h1 : term52 x y) : (term57 y P x) = (term70 P x).
Proof. exact (MK_COMB (@lem1483159 P y) (@lem1483180 P x y h1)). Qed.
Lemma lem1483183 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1483184 (P : real -> Prop) (x : real) : (term70 P x) = (P x).
Proof. exact (@lem1483183 (P x)). Qed.
Lemma lem1483185 (P : real -> Prop) (x : real) (y : real) (h1 : term52 x y) : (term57 y P x) = (P x).
Proof. exact (TRANS (@lem1483181 P x y h1) (@lem1483184 P x)). Qed.
Lemma lem1483186 (P : real -> Prop) (x : real) : (term68 P x) = (term68 P x).
Proof. exact (eq_refl (term68 P x)). Qed.
Lemma lem1483187 (P : real -> Prop) (x : real) (y : real) (h1 : term52 x y) : ((P x) = (term57 y P x)) = ((P x) = (P x)).
Proof. exact (MK_COMB (@lem1483186 P x) (@lem1483185 P x y h1)). Qed.
Lemma lem1483189 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1483190 (x : Prop) : (x = x) = True.
Proof. exact (@lem1483189 Prop x). Qed.
Lemma lem1483191 (P : real -> Prop) (x : real) : ((P x) = (P x)) = True.
Proof. exact (@lem1483190 (P x)). Qed.
Lemma lem1483192 (P : real -> Prop) (x : real) (y : real) (h1 : term52 x y) : ((P x) = (term57 y P x)) = True.
Proof. exact (TRANS (@lem1483187 P x y h1) (@lem1483191 P x)). Qed.
Lemma lem1483193 (P : real -> Prop) (x : real) (y : real) (h1 : term52 x y) : True = ((P x) = (term57 y P x)).
Proof. exact (SYM (@lem1483192 P x y h1)). Qed.
Lemma lem1483194 (P : real -> Prop) (x : real) (y : real) (h1 : term52 x y) : (P x) = (term57 y P x).
Proof. exact (EQ_MP (@lem1483193 P x y h1) (@lem0)). Qed.
Lemma lem1483195 (P : real -> Prop) (x : real) (y : real) (h1 : term52 x y) : (P x) = (term25 y P x).
Proof. exact (EQ_MP (@lem1483090 P x y h1) (@lem1483194 P x y h1)). Qed.
Lemma lem1483196 (P : real -> Prop) (x : real) (y : real) (h1 : term52 x y) : (term52 x y) = ((P x) = (term25 y P x)).
Proof. exact (prop_ext (fun h2 : term52 x y => @lem1483195 P x y h1) (fun h2 : (P x) = (term25 y P x) => @lem1483075 x y h1)). Qed.
Lemma lem1483197 (P : real -> Prop) (x : real) (y : real) (h1 : term52 x y) : (P x) = (term25 y P x).
Proof. exact (EQ_MP (@lem1483196 P x y h1) (@lem1483075 x y h1)). Qed.
Lemma lem1483198 (y : real) (P : real -> Prop) (x : real) : term36 y P x.
Proof. exact (fun h0 : term52 x y => @lem1483197 P x y h0). Qed.
Lemma lem1483199 (P : real -> Prop) (x : real) (y : real) (h1 : real_le x y) : (P y) = (term25 y P x).
Proof. exact (EQ_MP (@lem1483074 P x y h1) (@lem1483142 P x y h1)). Qed.
Lemma lem1483200 (P : real -> Prop) (x : real) (y : real) (h1 : real_le x y) : (real_le x y) = ((P y) = (term25 y P x)).
Proof. exact (prop_ext (fun h2 : real_le x y => @lem1483199 P x y h1) (fun h2 : (P y) = (term25 y P x) => @lem1483059 x y h1)). Qed.
Lemma lem1483201 (P : real -> Prop) (x : real) (y : real) (h1 : real_le x y) : (P y) = (term25 y P x).
Proof. exact (EQ_MP (@lem1483200 P x y h1) (@lem1483059 x y h1)). Qed.
Lemma lem1483202 (y : real) (P : real -> Prop) (x : real) : term40 y P x.
Proof. exact (fun h0 : real_le x y => @lem1483201 P x y h0). Qed.
Lemma lem1483203 (y : real) (P : real -> Prop) (x : real) : term43 y P x.
Proof. exact (conj (@lem1483202 y P x) (@lem1483198 y P x)). Qed.
Lemma lem1483204 (y : real) (P : real -> Prop) (x : real) : (term11 P y x) = (term25 y P x).
Proof. exact (EQ_MP (@lem1483058 y P x) (@lem1483203 y P x)). Qed.
Lemma lem1483205 (y : real) (P : real -> Prop) (x : real) : (term10 P x y) = (term24 y P x).
Proof. exact (EQ_MP (@lem1483040 y P x) (@lem1483204 y P x)). Qed.
