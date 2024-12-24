Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ABS_term_abbrevs.
Require Import real_abs_spec.
Require Import thm0_spec.
Require Import thm13473_spec.
Require Import thm1823_spec.
Require Import thm2299672_spec.
Require Import thm2299871_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2318064 (x : real) : term0 x.
Proof. exact (@lem1343359 x). Qed.
Lemma lem2318065 (x : real) : (term0 x) = ((real_abs x) = (term1 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2318066 (x : real) : (real_abs x) = (term1 x).
Proof. exact (EQ_MP (@lem2318065 x) (@lem2318064 x)). Qed.
Lemma lem2318067 : term2.
Proof. exact (fun x : real => @lem2318066 x). Qed.
Lemma lem2318068 (x : int) : term3 x.
Proof. exact (@lem2318067 (real_of_int x)). Qed.
Lemma lem2318069 (x : int) : (term3 x) = ((term4 x) = (term5 x)).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem2318070 (x : int) : (term4 x) = (term5 x).
Proof. exact (EQ_MP (@lem2318069 x) (@lem2318068 x)). Qed.
Lemma lem2318072 (x : int) : (term4 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2318073 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2318074 (x : int) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem2318073) (@lem2318072 x)). Qed.
Lemma lem2318076 (n : nat) : (real_of_num n) = (term9 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2318077 : term10 = term11.
Proof. exact (@lem2318076 (NUMERAL 0)). Qed.
Lemma lem2318078 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2318079 : term12 = term13.
Proof. exact (MK_COMB (@lem2318078) (@lem2318077)). Qed.
Lemma lem2318080 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2318081 (x : int) : (term14 x) = (term15 x).
Proof. exact (MK_COMB (@lem2318079) (@lem2318080 x)). Qed.
Lemma lem2318083 (x : int) (y : int) : (term16 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2318084 (x : int) : (term15 x) = (term17 x).
Proof. exact (@lem2318083 term18 x). Qed.
Lemma lem2318085 (x : int) : (term14 x) = (term17 x).
Proof. exact (TRANS (@lem2318081 x) (@lem2318084 x)). Qed.
Lemma lem2318086 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem2318087 (x : int) : (term19 x) = (term20 x).
Proof. exact (MK_COMB (@lem2318086) (@lem2318085 x)). Qed.
Lemma lem2318088 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2318089 (x : int) : (term21 x) = (term22 x).
Proof. exact (MK_COMB (@lem2318087 x) (@lem2318088 x)). Qed.
Lemma lem2318091 (x : int) : (term23 x) = (term24 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2318092 (x : int) : (term5 x) = (term25 x).
Proof. exact (MK_COMB (@lem2318089 x) (@lem2318091 x)). Qed.
Lemma lem2318094 (b : Prop) (x : int) (y : int) : (term26 b x y) = (term27 b x y).
Proof. exact (EQ_MP (@lem2299871 b x y) (@lem2299672 b x y)). Qed.
Lemma lem2318095 (x : int) : (term25 x) = (term28 x).
Proof. exact (@lem2318094 (term17 x) x (int_neg x)). Qed.
Lemma lem2318096 (x : int) : (term5 x) = (term28 x).
Proof. exact (TRANS (@lem2318092 x) (@lem2318095 x)). Qed.
Lemma lem2318097 (x : int) : ((term4 x) = (term5 x)) = ((term6 x) = (term28 x)).
Proof. exact (MK_COMB (@lem2318074 x) (@lem2318096 x)). Qed.
Lemma lem2318099 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2318100 (x : int) : ((term6 x) = (term28 x)) = ((int_abs x) = (term29 x)).
Proof. exact (@lem2318099 (int_abs x) (term29 x)). Qed.
Lemma lem2318101 (x : int) : ((term4 x) = (term5 x)) = ((int_abs x) = (term29 x)).
Proof. exact (TRANS (@lem2318097 x) (@lem2318100 x)). Qed.
Lemma lem2318102 (x : int) : (int_abs x) = (term29 x).
Proof. exact (EQ_MP (@lem2318101 x) (@lem2318070 x)). Qed.
Lemma lem2318103 (_474 : int) (_475 : Prop) (_476 : int -> Prop) (_477 : int) : (term30 _476 _475 _474 _477) = (term31 _474 _475 _476 _477).
Proof. exact (@lem13473 int _474 _475 _476 _477). Qed.
Lemma lem2318104 (_474 : int) (_475 : Prop) (x : int) (_477 : int) : (term32 x _475 _474 _477) = (term33 _474 _475 x _477).
Proof. exact (@lem2318103 _474 _475 (term34 x) _477). Qed.
Lemma lem2318105 (x : int) : (term35 x) = (term36 x).
Proof. exact (@lem2318104 x (term17 x) x (int_neg x)). Qed.
Lemma lem2318106 (x : int) : (term37 x) = (term38 x).
Proof. exact (eq_refl (term37 x)). Qed.
Lemma lem2318107 (x : int) : (term39 x) = (term39 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem2318108 (x : int) : (term40 x) = (term41 x).
Proof. exact (MK_COMB (@lem2318107 x) (@lem2318106 x)). Qed.
Lemma lem2318109 (x : int) : (term42 x) = (term43 x).
Proof. exact (eq_refl (term42 x)). Qed.
Lemma lem2318110 (x : int) : (term44 x) = (term44 x).
Proof. exact (eq_refl (term44 x)). Qed.
Lemma lem2318111 (x : int) : (term45 x) = (term46 x).
Proof. exact (MK_COMB (@lem2318110 x) (@lem2318109 x)). Qed.
Lemma lem2318112 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2318113 (x : int) : (term47 x) = (term48 x).
Proof. exact (MK_COMB (@lem2318112) (@lem2318111 x)). Qed.
Lemma lem2318114 (x : int) : (term36 x) = (term49 x).
Proof. exact (MK_COMB (@lem2318113 x) (@lem2318108 x)). Qed.
Lemma lem2318115 (x : int) : (term35 x) = (term50 x).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem2318116 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2318117 (x : int) : (term51 x) = (term52 x).
Proof. exact (MK_COMB (@lem2318116) (@lem2318115 x)). Qed.
Lemma lem2318118 (x : int) : ((term35 x) = (term36 x)) = ((term50 x) = (term49 x)).
Proof. exact (MK_COMB (@lem2318117 x) (@lem2318114 x)). Qed.
Lemma lem2318119 (x : int) : (term50 x) = (term49 x).
Proof. exact (EQ_MP (@lem2318118 x) (@lem2318105 x)). Qed.
Lemma lem2318120 (x : int) : (term49 x) = (term50 x).
Proof. exact (SYM (@lem2318119 x)). Qed.
Lemma lem2318158 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem2318159 (x : int) : (term43 x) = True.
Proof. exact (@lem2318158 ((int_abs x) = x)). Qed.
Lemma lem2318160 (x : int) : True = (term43 x).
Proof. exact (SYM (@lem2318159 x)). Qed.
Lemma lem2318165 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem2318166 (x : int) : (term38 x) = True.
Proof. exact (@lem2318165 ((int_abs x) = (int_neg x))). Qed.
Lemma lem2318167 (x : int) : True = (term38 x).
Proof. exact (SYM (@lem2318166 x)). Qed.
Lemma lem2318169 (x : int) : term38 x.
Proof. exact (EQ_MP (@lem2318167 x) (@lem0)). Qed.
Lemma lem2318170 (x : int) : term41 x.
Proof. exact (fun h0 : term53 x => @lem2318169 x). Qed.
Lemma lem2318171 (x : int) : term43 x.
Proof. exact (EQ_MP (@lem2318160 x) (@lem0)). Qed.
Lemma lem2318172 (x : int) : term46 x.
Proof. exact (fun h0 : term17 x => @lem2318171 x). Qed.
Lemma lem2318173 (x : int) : term49 x.
Proof. exact (conj (@lem2318172 x) (@lem2318170 x)). Qed.
Lemma lem2318174 (x : int) : term50 x.
Proof. exact (EQ_MP (@lem2318120 x) (@lem2318173 x)). Qed.
Lemma lem2318175 (x : int) : (int_abs x) = (term29 x).
Proof. exact (@lem2318174 x (@lem2318102 x)). Qed.
Lemma lem2318180 : term54.
Proof. exact (fun x : int => @lem2318175 x). Qed.
