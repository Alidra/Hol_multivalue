Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import num_FINITE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import FINITE_NUMSEG_LE_spec.
Require Import FINITE_SUBSET_spec.
Require Import IN_INSERT_spec.
Require Import LE_CASES_spec.
Require Import LE_TRANS_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import SUBSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm32_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem4622062 (n : nat) : term0 n.
Proof. exact (@lem4621993 n). Qed.
Lemma lem4622063 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem4622064 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem4622063 n) (@lem4622062 n)). Qed.
Lemma lem4622065 (n : nat) : (term1 n) = ((term1 n) = True).
Proof. exact (@lem7 (term1 n)). Qed.
Lemma lem4622067 {A : Type'} (h1 : term2 A) : term2 A.
Proof. exact (h1). Qed.
Lemma lem4622068 {A : Type'} (s : A -> Prop) (h1 : term2 A) : term3 A s.
Proof. exact (@lem4622067 A h1 s). Qed.
Lemma lem4622069 {A : Type'} (s : A -> Prop) : (term3 A s) = (term4 A s).
Proof. exact (eq_refl (term3 A s)). Qed.
Lemma lem4622070 {A : Type'} (s : A -> Prop) (h1 : term2 A) : term4 A s.
Proof. exact (EQ_MP (@lem4622069 A s) (@lem4622068 A s h1)). Qed.
Lemma lem4622071 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term2 A) : term5 A s t.
Proof. exact (@lem4622070 A s h1 t). Qed.
Lemma lem4622072 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term5 A s t) = (term6 A t s).
Proof. exact (eq_refl (term5 A s t)). Qed.
Lemma lem4622073 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term2 A) : term6 A t s.
Proof. exact (EQ_MP (@lem4622072 A t s) (@lem4622071 A s t h1)). Qed.
Lemma lem4622074 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term7 A s t) : term7 A s t.
Proof. exact (h1). Qed.
Lemma lem4622075 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term2 A) (h2 : term7 A s t) : @FINITE A s.
Proof. exact (@lem4622073 A t s h1 (@lem4622074 A s t h2)). Qed.
Lemma lem4622076 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term7 A s t) : term8 A s.
Proof. exact (fun h0 : term2 A => @lem4622075 A s t h0 h1). Qed.
Lemma lem4622077 {A : Type'} (s : A -> Prop) (h1 : term9 A s) : term9 A s.
Proof. exact (h1). Qed.
Lemma lem4622078 {A : Type'} (s : A -> Prop) (h1 : term9 A s) : term8 A s.
Proof. exact (ex_elim (@lem4622077 A s h1) (fun t : A -> Prop => fun h0 : term10 A s t => @lem4622076 A s t h0)). Qed.
Lemma lem4622079 {A : Type'} (h1 : term2 A) : term2 A.
Proof. exact (h1). Qed.
Lemma lem4622080 {A : Type'} (s : A -> Prop) (h1 : term2 A) (h2 : term9 A s) : @FINITE A s.
Proof. exact (@lem4622078 A s h2 (@lem4622079 A h1)). Qed.
Lemma lem4622081 {A : Type'} (s : A -> Prop) (h1 : term2 A) : term11 A s.
Proof. exact (fun h0 : term9 A s => @lem4622080 A s h1 h0). Qed.
Lemma lem4622082 {A : Type'} (h1 : term2 A) : term12 A.
Proof. exact (fun s : A -> Prop => @lem4622081 A s h1). Qed.
Lemma lem4622083 {A : Type'} : term13 A.
Proof. exact (fun h0 : term2 A => @lem4622082 A h0). Qed.
Lemma lem4622084 {A : Type'} : term12 A.
Proof. exact (@lem4622083 A (@lem3599924 A)). Qed.
Lemma lem4622085 {A : Type'} (s : A -> Prop) : term14 A s.
Proof. exact (@lem4622084 A s). Qed.
Lemma lem4622086 {A : Type'} (s : A -> Prop) : (term14 A s) = (term11 A s).
Proof. exact (eq_refl (term14 A s)). Qed.
Lemma lem4622088 (t1 : Prop) : term15 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4622089 (t1 : Prop) : (term15 t1) = (term16 t1).
Proof. exact (eq_refl (term15 t1)). Qed.
Lemma lem4622090 (t1 : Prop) : term16 t1.
Proof. exact (EQ_MP (@lem4622089 t1) (@lem4622088 t1)). Qed.
Lemma lem4622091 (t1 : Prop) (t2 : Prop) : term17 t1 t2.
Proof. exact (@lem4622090 t1 t2). Qed.
Lemma lem4622092 (t1 : Prop) (t2 : Prop) : (term17 t1 t2) = (term18 t1 t2).
Proof. exact (eq_refl (term17 t1 t2)). Qed.
Lemma lem4622093 (t1 : Prop) (t2 : Prop) : term18 t1 t2.
Proof. exact (EQ_MP (@lem4622092 t1 t2) (@lem4622091 t1 t2)). Qed.
Lemma lem4622094 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term19 t1 t2 t3.
Proof. exact (@lem4622093 t1 t2 t3). Qed.
Lemma lem4622095 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term19 t1 t2 t3) = ((term20 t1 t2 t3) = (term21 t1 t2 t3)).
Proof. exact (eq_refl (term19 t1 t2 t3)). Qed.
Lemma lem4622096 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term20 t1 t2 t3) = (term21 t1 t2 t3).
Proof. exact (EQ_MP (@lem4622095 t1 t2 t3) (@lem4622094 t1 t2 t3)). Qed.
Lemma lem4622097 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term21 t1 t2 t3) = (term20 t1 t2 t3).
Proof. exact (SYM (@lem4622096 t1 t2 t3)). Qed.
Lemma lem4622098 {A : Type'} (x : A) : term22 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem4622099 {A : Type'} (x : A) : (term22 A x) = (term23 A x).
Proof. exact (eq_refl (term22 A x)). Qed.
Lemma lem4622100 {A : Type'} (x : A) : term23 A x.
Proof. exact (EQ_MP (@lem4622099 A x) (@lem4622098 A x)). Qed.
Lemma lem4622101 {A : Type'} (x : A) : term24 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem4622103 {A : Type'} (x : A) : term25 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem4622104 {A : Type'} (x : A) : (term25 A x) = (term26 A x).
Proof. exact (eq_refl (term25 A x)). Qed.
Lemma lem4622105 {A : Type'} (x : A) : term26 A x.
Proof. exact (EQ_MP (@lem4622104 A x) (@lem4622103 A x)). Qed.
Lemma lem4622106 {A : Type'} (x : A) (y : A) : term27 A x y.
Proof. exact (@lem4622105 A x y). Qed.
Lemma lem4622107 {A : Type'} (y : A) (x : A) : (term27 A x y) = (term28 A y x).
Proof. exact (eq_refl (term27 A x y)). Qed.
Lemma lem4622108 {A : Type'} (y : A) (x : A) : term28 A y x.
Proof. exact (EQ_MP (@lem4622107 A y x) (@lem4622106 A x y)). Qed.
Lemma lem4622109 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term29 A y x s.
Proof. exact (@lem4622108 A y x s). Qed.
Lemma lem4622110 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term29 A y x s) = ((term30 A x y s) = (term31 A y x s)).
Proof. exact (eq_refl (term29 A y x s)). Qed.
Lemma lem4622112 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (h1). Qed.
Lemma lem4622113 {A : Type'} (P : type686 A) (h1 : term32 A) : term33 A P.
Proof. exact (@lem4622112 A h1 P). Qed.
Lemma lem4622114 {A : Type'} (P : type686 A) : (term33 A P) = (term34 A P).
Proof. exact (eq_refl (term33 A P)). Qed.
Lemma lem4622115 {A : Type'} (P : type686 A) (h1 : term32 A) : term34 A P.
Proof. exact (EQ_MP (@lem4622114 A P) (@lem4622113 A P h1)). Qed.
Lemma lem4622116 {A : Type'} (P : type686 A) (h1 : term35 A P) : term35 A P.
Proof. exact (h1). Qed.
Lemma lem4622117 {A : Type'} (P : type686 A) (h1 : term32 A) (h2 : term35 A P) : term36 A P.
Proof. exact (@lem4622115 A P h1 (@lem4622116 A P h2)). Qed.
Lemma lem4622118 {A : Type'} (P : type686 A) (h1 : term35 A P) : term37 A P.
Proof. exact (fun h0 : term32 A => @lem4622117 A P h0 h1). Qed.
Lemma lem4622119 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (h1). Qed.
Lemma lem4622120 {A : Type'} (P : type686 A) (h1 : term32 A) (h2 : term35 A P) : term36 A P.
Proof. exact (@lem4622118 A P h2 (@lem4622119 A h1)). Qed.
Lemma lem4622121 {A : Type'} (P : type686 A) (h1 : term32 A) : term34 A P.
Proof. exact (fun h0 : term35 A P => @lem4622120 A P h1 h0). Qed.
Lemma lem4622122 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (fun P : type686 A => @lem4622121 A P h1). Qed.
Lemma lem4622123 {A : Type'} : term38 A.
Proof. exact (fun h0 : term32 A => @lem4622122 A h0). Qed.
Lemma lem4622124 {A : Type'} : term32 A.
Proof. exact (@lem4622123 A (@lem3558722 A)). Qed.
Lemma lem4622125 {A : Type'} (P : type686 A) : term33 A P.
Proof. exact (@lem4622124 A P). Qed.
Lemma lem4622126 {A : Type'} (P : type686 A) : (term33 A P) = (term34 A P).
Proof. exact (eq_refl (term33 A P)). Qed.
Lemma lem4622129 {A : Type'} (P : type686 A) : term34 A P.
Proof. exact (EQ_MP (@lem4622126 A P) (@lem4622125 A P)). Qed.
Lemma lem4622130 (P : type993) : term39 P.
Proof. exact (@lem4622129 nat P). Qed.
Lemma lem4622131 : term40.
Proof. exact (@lem4622130 term41). Qed.
Lemma lem4622132 : term42 = term43.
Proof. exact (eq_refl term42). Qed.
Lemma lem4622133 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4622134 : term44 = term45.
Proof. exact (MK_COMB (@lem4622133) (@lem4622132)). Qed.
Lemma lem4622135 (s : nat -> Prop) : (term46 s) = (term47 s).
Proof. exact (eq_refl (term46 s)). Qed.
Lemma lem4622136 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4622137 (s : nat -> Prop) : (term48 s) = (term49 s).
Proof. exact (MK_COMB (@lem4622136) (@lem4622135 s)). Qed.
Lemma lem4622138 (x : nat) (s : nat -> Prop) : (term50 x s) = (term50 x s).
Proof. exact (eq_refl (term50 x s)). Qed.
Lemma lem4622139 (x : nat) (s : nat -> Prop) : (term51 x s) = (term52 x s).
Proof. exact (MK_COMB (@lem4622137 s) (@lem4622138 x s)). Qed.
Lemma lem4622140 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4622141 (x : nat) (s : nat -> Prop) : (term53 x s) = (term54 x s).
Proof. exact (MK_COMB (@lem4622140) (@lem4622139 x s)). Qed.
Lemma lem4622142 (x : nat) (s : nat -> Prop) : (term55 x s) = (term56 x s).
Proof. exact (eq_refl (term55 x s)). Qed.
Lemma lem4622143 (x : nat) (s : nat -> Prop) : (term57 x s) = (term58 x s).
Proof. exact (MK_COMB (@lem4622141 x s) (@lem4622142 x s)). Qed.
Lemma lem4622144 (x : nat) : (term59 x) = (term60 x).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4622143 x s)). Qed.
Lemma lem4622145 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4622146 (x : nat) : (term61 x) = (term62 x).
Proof. exact (MK_COMB (@lem4622145) (@lem4622144 x)). Qed.
Lemma lem4622147 : term63 = term64.
Proof. exact (fun_ext (fun x : nat => @lem4622146 x)). Qed.
Lemma lem4622148 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4622149 : term65 = term66.
Proof. exact (MK_COMB (@lem4622148) (@lem4622147)). Qed.
Lemma lem4622150 : term67 = term68.
Proof. exact (MK_COMB (@lem4622134) (@lem4622149)). Qed.
Lemma lem4622151 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4622152 : term69 = term70.
Proof. exact (MK_COMB (@lem4622151) (@lem4622150)). Qed.
Lemma lem4622153 (s : nat -> Prop) : (term46 s) = (term47 s).
Proof. exact (eq_refl (term46 s)). Qed.
Lemma lem4622154 (s : nat -> Prop) : (term71 s) = (term71 s).
Proof. exact (eq_refl (term71 s)). Qed.
Lemma lem4622155 (s : nat -> Prop) : (term72 s) = (term73 s).
Proof. exact (MK_COMB (@lem4622154 s) (@lem4622153 s)). Qed.
Lemma lem4622156 : term74 = term75.
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4622155 s)). Qed.
Lemma lem4622157 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4622158 : term76 = term77.
Proof. exact (MK_COMB (@lem4622157) (@lem4622156)). Qed.
Lemma lem4622159 : term40 = term78.
Proof. exact (MK_COMB (@lem4622152) (@lem4622158)). Qed.
Lemma lem4622160 : term78.
Proof. exact (EQ_MP (@lem4622159) (@lem4622131)). Qed.
Lemma lem4622174 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4622101 A x (@lem4622100 A x)). Qed.
Lemma lem4622175 (x : nat) : (@IN nat x (@EMPTY nat)) = False.
Proof. exact (@lem4622174 nat x). Qed.
Lemma lem4622176 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4622177 (x : nat) : (term79 x) = (imp False).
Proof. exact (MK_COMB (@lem4622176) (@lem4622175 x)). Qed.
Lemma lem4622178 (x : nat) (a : nat) : (Peano.le x a) = (Peano.le x a).
Proof. exact (eq_refl (Peano.le x a)). Qed.
Lemma lem4622179 (x : nat) (a : nat) : (term80 x a) = (term81 x a).
Proof. exact (MK_COMB (@lem4622177 x) (@lem4622178 x a)). Qed.
Lemma lem4622181 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4622182 (x : nat) (a : nat) : (term81 x a) = True.
Proof. exact (@lem4622181 (Peano.le x a)). Qed.
Lemma lem4622183 (x : nat) (a : nat) : (term80 x a) = True.
Proof. exact (TRANS (@lem4622179 x a) (@lem4622182 x a)). Qed.
Lemma lem4622184 (a : nat) : (term82 a) = term83.
Proof. exact (fun_ext (fun x : nat => @lem4622183 x a)). Qed.
Lemma lem4622185 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4622186 (a : nat) : (term84 a) = term85.
Proof. exact (MK_COMB (@lem4622185) (@lem4622184 a)). Qed.
Lemma lem4622188 {A : Type'} (t : Prop) : (term86 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4622189 (t : Prop) : (term87 t) = t.
Proof. exact (@lem4622188 nat t). Qed.
Lemma lem4622190 : term85 = True.
Proof. exact (@lem4622189 True). Qed.
Lemma lem4622191 (a : nat) : (term84 a) = True.
Proof. exact (TRANS (@lem4622186 a) (@lem4622190)). Qed.
Lemma lem4622192 : term88 = term83.
Proof. exact (fun_ext (fun a : nat => @lem4622191 a)). Qed.
Lemma lem4622193 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4622194 : term43 = term89.
Proof. exact (MK_COMB (@lem4622193) (@lem4622192)). Qed.
Lemma lem4622196 {A : Type'} (t : Prop) : (term90 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem4622197 (t : Prop) : (term91 t) = t.
Proof. exact (@lem4622196 nat t). Qed.
Lemma lem4622198 : term89 = True.
Proof. exact (@lem4622197 True). Qed.
Lemma lem4622199 : term43 = True.
Proof. exact (TRANS (@lem4622194) (@lem4622198)). Qed.
Lemma lem4622200 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4622201 : term45 = (and True).
Proof. exact (MK_COMB (@lem4622200) (@lem4622199)). Qed.
Lemma lem4622237 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term30 A x y s) = (term31 A y x s).
Proof. exact (EQ_MP (@lem4622110 A y x s) (@lem4622109 A y x s)). Qed.
Lemma lem4622238 (y : nat) (x : nat) (s : nat -> Prop) : (term92 x y s) = (term93 y x s).
Proof. exact (@lem4622237 nat y x s). Qed.
Lemma lem4622239 (x : nat) (x' : nat) (s : nat -> Prop) : (term92 x' x s) = (term93 x x' s).
Proof. exact (@lem4622238 x x' s). Qed.
Lemma lem4622244 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4622245 (x : nat) (x' : nat) (s : nat -> Prop) : (term94 x' x s) = (term95 x x' s).
Proof. exact (MK_COMB (@lem4622244) (@lem4622239 x x' s)). Qed.
Lemma lem4622246 (x' : nat) (a : nat) : (Peano.le x' a) = (Peano.le x' a).
Proof. exact (eq_refl (Peano.le x' a)). Qed.
Lemma lem4622247 (x : nat) (s : nat -> Prop) (x' : nat) (a : nat) : (term96 x s x' a) = (term97 x s x' a).
Proof. exact (MK_COMB (@lem4622245 x x' s) (@lem4622246 x' a)). Qed.
Lemma lem4622250 (x : nat) (s : nat -> Prop) (a : nat) : (term98 x s a) = (term99 x s a).
Proof. exact (fun_ext (fun x' : nat => @lem4622247 x s x' a)). Qed.
Lemma lem4622251 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4622252 (x : nat) (s : nat -> Prop) (a : nat) : (term100 x s a) = (term101 x s a).
Proof. exact (MK_COMB (@lem4622251) (@lem4622250 x s a)). Qed.
Lemma lem4622257 (x : nat) (s : nat -> Prop) : (term102 x s) = (term103 x s).
Proof. exact (fun_ext (fun a : nat => @lem4622252 x s a)). Qed.
Lemma lem4622258 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4622259 (x : nat) (s : nat -> Prop) : (term56 x s) = (term104 x s).
Proof. exact (MK_COMB (@lem4622258) (@lem4622257 x s)). Qed.
Lemma lem4622264 (x : nat) (s : nat -> Prop) : (term54 x s) = (term54 x s).
Proof. exact (eq_refl (term54 x s)). Qed.
Lemma lem4622265 (x : nat) (s : nat -> Prop) : (term58 x s) = (term105 x s).
Proof. exact (MK_COMB (@lem4622264 x s) (@lem4622259 x s)). Qed.
Lemma lem4622268 (x : nat) : (term60 x) = (term106 x).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4622265 x s)). Qed.
Lemma lem4622269 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4622270 (x : nat) : (term62 x) = (term107 x).
Proof. exact (MK_COMB (@lem4622269) (@lem4622268 x)). Qed.
Lemma lem4622275 : term64 = term108.
Proof. exact (fun_ext (fun x : nat => @lem4622270 x)). Qed.
Lemma lem4622276 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4622277 : term66 = term109.
Proof. exact (MK_COMB (@lem4622276) (@lem4622275)). Qed.
Lemma lem4622282 : term68 = term110.
Proof. exact (MK_COMB (@lem4622201) (@lem4622277)). Qed.
Lemma lem4622284 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4622285 : term110 = term109.
Proof. exact (@lem4622284 term109). Qed.
Lemma lem4622324 : term68 = term109.
Proof. exact (TRANS (@lem4622282) (@lem4622285)). Qed.
Lemma lem4622325 : term109 = term68.
Proof. exact (SYM (@lem4622324)). Qed.
Lemma lem4622327 (p : Prop) : p = (term111 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4622328 : term109 = term112.
Proof. exact (@lem4622327 term109). Qed.
Lemma lem4622329 : term112 = term109.
Proof. exact (SYM (@lem4622328)). Qed.
Lemma lem4622330 (h1 : term113) : term113.
Proof. exact (h1). Qed.
Lemma lem4622333 (h1 : term114) : term114.
Proof. exact (h1). Qed.
Lemma lem4622334 : term115.
Proof. exact (fun h0 : term114 => @lem4622333 h0). Qed.
Lemma lem4622335 (h1 : term115) : term115.
Proof. exact (h1). Qed.
Lemma lem4622336 (h1 : term114) : term114.
Proof. exact (h1). Qed.
Lemma lem4622337 (h1 : term114) (h2 : term115) : term114.
Proof. exact (@lem4622335 h2 (@lem4622336 h1)). Qed.
Lemma lem4622338 (h1 : term114) : term116.
Proof. exact (fun h0 : term115 => @lem4622337 h1 h0). Qed.
Lemma lem4622339 (h1 : term115) : term115.
Proof. exact (h1). Qed.
Lemma lem4622340 (h1 : term114) (h2 : term115) : term114.
Proof. exact (@lem4622338 h1 (@lem4622339 h2)). Qed.
Lemma lem4622341 (h1 : term115) : term115.
Proof. exact (fun h0 : term114 => @lem4622340 h0 h1). Qed.
Lemma lem4622342 : term117.
Proof. exact (fun h0 : term115 => @lem4622341 h0). Qed.
Lemma lem4622345 : term115.
Proof. exact (@lem4622342 (@lem4622334)). Qed.
Lemma lem4622403 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4622404 : term118 = term119.
Proof. exact (@lem4622403 term120). Qed.
Lemma lem4622459 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem4622460 : term122 = term123.
Proof. exact (MK_COMB (@lem4622459) (@lem4622404)). Qed.
Lemma lem4622463 : term124 = term124.
Proof. exact (eq_refl term124). Qed.
Lemma lem4622470 : term114 = term125.
Proof. exact (MK_COMB (@lem4622463) (@lem4622460)). Qed.
Lemma lem4622475 (n : nat) (m : nat) : (term126 n m) = (term126 n m).
Proof. exact (eq_refl (term126 n m)). Qed.
Lemma lem4622476 (m : nat) : (term127 m) = (term127 m).
Proof. exact (fun_ext (fun n : nat => @lem4622475 n m)). Qed.
Lemma lem4622477 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4622478 (m : nat) : (term128 m) = (term128 m).
Proof. exact (MK_COMB (@lem4622477) (@lem4622476 m)). Qed.
Lemma lem4622479 : term129 = term129.
Proof. exact (fun_ext (fun m : nat => @lem4622478 m)). Qed.
Lemma lem4622480 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4622481 : term120 = term120.
Proof. exact (MK_COMB (@lem4622480) (@lem4622479)). Qed.
Lemma lem4622482 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4622483 : term119 = term119.
Proof. exact (MK_COMB (@lem4622482) (@lem4622481)). Qed.
Lemma lem4622492 (n : nat) (m : nat) (p : nat) : (term130 n m p) = (term130 n m p).
Proof. exact (eq_refl (term130 n m p)). Qed.
Lemma lem4622493 (n : nat) (m : nat) : (term131 n m) = (term131 n m).
Proof. exact (fun_ext (fun p : nat => @lem4622492 n m p)). Qed.
Lemma lem4622494 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4622495 (n : nat) (m : nat) : (term132 n m) = (term132 n m).
Proof. exact (MK_COMB (@lem4622494) (@lem4622493 n m)). Qed.
Lemma lem4622496 (m : nat) : (term133 m) = (term133 m).
Proof. exact (fun_ext (fun n : nat => @lem4622495 n m)). Qed.
Lemma lem4622497 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4622498 (m : nat) : (term134 m) = (term134 m).
Proof. exact (MK_COMB (@lem4622497) (@lem4622496 m)). Qed.
Lemma lem4622499 : term135 = term135.
Proof. exact (fun_ext (fun m : nat => @lem4622498 m)). Qed.
Lemma lem4622500 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4622501 : term136 = term136.
Proof. exact (MK_COMB (@lem4622500) (@lem4622499)). Qed.
Lemma lem4622502 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4622503 : term121 = term121.
Proof. exact (MK_COMB (@lem4622502) (@lem4622501)). Qed.
Lemma lem4622504 : term123 = term123.
Proof. exact (MK_COMB (@lem4622503) (@lem4622483)). Qed.
Lemma lem4622513 (x : nat) (s : nat -> Prop) (x' : nat) (a : nat) : (term97 x s x' a) = (term97 x s x' a).
Proof. exact (eq_refl (term97 x s x' a)). Qed.
Lemma lem4622514 (x : nat) (s : nat -> Prop) (a : nat) : (term99 x s a) = (term99 x s a).
Proof. exact (fun_ext (fun x' : nat => @lem4622513 x s x' a)). Qed.
Lemma lem4622515 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4622516 (x : nat) (s : nat -> Prop) (a : nat) : (term101 x s a) = (term101 x s a).
Proof. exact (MK_COMB (@lem4622515) (@lem4622514 x s a)). Qed.
Lemma lem4622517 (x : nat) (s : nat -> Prop) : (term103 x s) = (term103 x s).
Proof. exact (fun_ext (fun a : nat => @lem4622516 x s a)). Qed.
Lemma lem4622518 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4622519 (x : nat) (s : nat -> Prop) : (term104 x s) = (term104 x s).
Proof. exact (MK_COMB (@lem4622518) (@lem4622517 x s)). Qed.
Lemma lem4622526 (x : nat) (s : nat -> Prop) : (term50 x s) = (term50 x s).
Proof. exact (eq_refl (term50 x s)). Qed.
Lemma lem4622531 (s : nat -> Prop) (x : nat) (a : nat) : (term137 s x a) = (term137 s x a).
Proof. exact (eq_refl (term137 s x a)). Qed.
Lemma lem4622532 (s : nat -> Prop) (a : nat) : (term138 s a) = (term138 s a).
Proof. exact (fun_ext (fun x : nat => @lem4622531 s x a)). Qed.
Lemma lem4622533 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4622534 (s : nat -> Prop) (a : nat) : (term139 s a) = (term139 s a).
Proof. exact (MK_COMB (@lem4622533) (@lem4622532 s a)). Qed.
Lemma lem4622535 (s : nat -> Prop) : (term140 s) = (term140 s).
Proof. exact (fun_ext (fun a : nat => @lem4622534 s a)). Qed.
Lemma lem4622536 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4622537 (s : nat -> Prop) : (term47 s) = (term47 s).
Proof. exact (MK_COMB (@lem4622536) (@lem4622535 s)). Qed.
Lemma lem4622538 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4622539 (s : nat -> Prop) : (term49 s) = (term49 s).
Proof. exact (MK_COMB (@lem4622538) (@lem4622537 s)). Qed.
Lemma lem4622540 (x : nat) (s : nat -> Prop) : (term52 x s) = (term52 x s).
Proof. exact (MK_COMB (@lem4622539 s) (@lem4622526 x s)). Qed.
Lemma lem4622541 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4622542 (x : nat) (s : nat -> Prop) : (term54 x s) = (term54 x s).
Proof. exact (MK_COMB (@lem4622541) (@lem4622540 x s)). Qed.
Lemma lem4622543 (x : nat) (s : nat -> Prop) : (term105 x s) = (term105 x s).
Proof. exact (MK_COMB (@lem4622542 x s) (@lem4622519 x s)). Qed.
Lemma lem4622544 (x : nat) : (term106 x) = (term106 x).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4622543 x s)). Qed.
Lemma lem4622545 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem4622546 (x : nat) : (term107 x) = (term107 x).
Proof. exact (MK_COMB (@lem4622545) (@lem4622544 x)). Qed.
Lemma lem4622547 : term108 = term108.
Proof. exact (fun_ext (fun x : nat => @lem4622546 x)). Qed.
Lemma lem4622548 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4622549 : term109 = term109.
Proof. exact (MK_COMB (@lem4622548) (@lem4622547)). Qed.
Lemma lem4622550 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4622551 : term113 = term113.
Proof. exact (MK_COMB (@lem4622550) (@lem4622549)). Qed.
Lemma lem4622552 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4622553 : term124 = term124.
Proof. exact (MK_COMB (@lem4622552) (@lem4622551)). Qed.
Lemma lem4622554 : term125 = term125.
Proof. exact (MK_COMB (@lem4622553) (@lem4622504)). Qed.
Lemma lem4622645 : term114 = term125.
Proof. exact (TRANS (@lem4622470) (@lem4622554)). Qed.
Lemma lem4622646 : term125 = term114.
Proof. exact (SYM (@lem4622645)). Qed.
Lemma lem4622647 (h1 : term113) : term113.
Proof. exact (h1). Qed.
Lemma lem4622648 (h1 : term136) : term136.
Proof. exact (h1). Qed.
Lemma lem4622649 (h1 : term120) : term120.
Proof. exact (h1). Qed.
Lemma lem4622656 (s : nat -> Prop) (x : nat) (a : nat) : (term137 s x a) = (term141 s x a).
Proof. exact (@lem17265 (@IN nat x s) (Peano.le x a)). Qed.
Lemma lem4622657 (s : nat -> Prop) (a : nat) : (term138 s a) = (term142 s a).
Proof. exact (fun_ext (fun x : nat => @lem4622656 s x a)). Qed.
Lemma lem4622658 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4622659 (s : nat -> Prop) (a : nat) : (term139 s a) = (term143 s a).
Proof. exact (MK_COMB (@lem4622658) (@lem4622657 s a)). Qed.
Lemma lem4622660 (s : nat -> Prop) : (term140 s) = (term144 s).
Proof. exact (fun_ext (fun a : nat => @lem4622659 s a)). Qed.
Lemma lem4622661 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4622662 (s : nat -> Prop) : (term47 s) = (term145 s).
Proof. exact (MK_COMB (@lem4622661) (@lem4622660 s)). Qed.
Lemma lem4622667 (x : nat) (s : nat -> Prop) : (term50 x s) = (term50 x s).
Proof. exact (eq_refl (term50 x s)). Qed.
Lemma lem4622668 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4622669 (s : nat -> Prop) : (term49 s) = (term146 s).
Proof. exact (MK_COMB (@lem4622668) (@lem4622662 s)). Qed.
Lemma lem4622670 (x : nat) (s : nat -> Prop) : (term52 x s) = (term147 x s).
Proof. exact (MK_COMB (@lem4622669 s) (@lem4622667 x s)). Qed.
Lemma lem4622681 (x : nat) (s : nat -> Prop) (x' : nat) (a : nat) : (term148 x s x' a) = (term149 x s x' a).
Proof. exact (@lem17362 (term93 x x' s) (Peano.le x' a)). Qed.
Lemma lem4622682 (P : nat -> Prop) : (term150 P) = (term151 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem4622683 (x : nat) (s : nat -> Prop) (a : nat) : (term152 x s a) = (term153 x s a).
Proof. exact (@lem4622682 (term99 x s a)). Qed.
Lemma lem4622684 (x : nat) (s : nat -> Prop) (x' : nat) (a : nat) : (term154 x s a x') = (term97 x s x' a).
Proof. exact (eq_refl (term154 x s a x')). Qed.
Lemma lem4622685 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4622686 (x : nat) (s : nat -> Prop) (x' : nat) (a : nat) : (term155 x s a x') = (term148 x s x' a).
Proof. exact (MK_COMB (@lem4622685) (@lem4622684 x s x' a)). Qed.
Lemma lem4622687 (x : nat) (s : nat -> Prop) (x' : nat) (a : nat) : (term155 x s a x') = (term149 x s x' a).
Proof. exact (TRANS (@lem4622686 x s x' a) (@lem4622681 x s x' a)). Qed.
Lemma lem4622688 (x : nat) (s : nat -> Prop) (a : nat) : (term156 x s a) = (term157 x s a).
Proof. exact (fun_ext (fun x' : nat => @lem4622687 x s x' a)). Qed.
Lemma lem4622689 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4622690 (x : nat) (s : nat -> Prop) (a : nat) : (term153 x s a) = (term158 x s a).
Proof. exact (MK_COMB (@lem4622689) (@lem4622688 x s a)). Qed.
Lemma lem4622691 (x : nat) (s : nat -> Prop) (a : nat) : (term152 x s a) = (term158 x s a).
Proof. exact (TRANS (@lem4622683 x s a) (@lem4622690 x s a)). Qed.
Lemma lem4622692 (P : nat -> Prop) : (term159 P) = (term160 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem4622693 (x : nat) (s : nat -> Prop) : (term161 x s) = (term162 x s).
Proof. exact (@lem4622692 (term103 x s)). Qed.
Lemma lem4622694 (x : nat) (s : nat -> Prop) (a : nat) : (term163 x s a) = (term101 x s a).
Proof. exact (eq_refl (term163 x s a)). Qed.
Lemma lem4622695 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4622696 (x : nat) (s : nat -> Prop) (a : nat) : (term164 x s a) = (term152 x s a).
Proof. exact (MK_COMB (@lem4622695) (@lem4622694 x s a)). Qed.
Lemma lem4622697 (x : nat) (s : nat -> Prop) (a : nat) : (term164 x s a) = (term158 x s a).
Proof. exact (TRANS (@lem4622696 x s a) (@lem4622691 x s a)). Qed.
Lemma lem4622698 (x : nat) (s : nat -> Prop) : (term165 x s) = (term166 x s).
Proof. exact (fun_ext (fun a : nat => @lem4622697 x s a)). Qed.
Lemma lem4622699 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4622700 (x : nat) (s : nat -> Prop) : (term162 x s) = (term167 x s).
Proof. exact (MK_COMB (@lem4622699) (@lem4622698 x s)). Qed.
Lemma lem4622701 (x : nat) (s : nat -> Prop) : (term161 x s) = (term167 x s).
Proof. exact (TRANS (@lem4622693 x s) (@lem4622700 x s)). Qed.
Lemma lem4622702 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4622703 (x : nat) (s : nat -> Prop) : (term168 x s) = (term169 x s).
Proof. exact (MK_COMB (@lem4622702) (@lem4622670 x s)). Qed.
Lemma lem4622704 (x : nat) (s : nat -> Prop) : (term170 x s) = (term171 x s).
Proof. exact (MK_COMB (@lem4622703 x s) (@lem4622701 x s)). Qed.
Lemma lem4622705 (x : nat) (s : nat -> Prop) : (term172 x s) = (term170 x s).
Proof. exact (@lem17362 (term52 x s) (term104 x s)). Qed.
Lemma lem4622706 (x : nat) (s : nat -> Prop) : (term172 x s) = (term171 x s).
Proof. exact (TRANS (@lem4622705 x s) (@lem4622704 x s)). Qed.
Lemma lem4622707 (P : type993) : (term173 P) = (term174 P).
Proof. exact (@lem18392 (nat -> Prop) P). Qed.
Lemma lem4622708 (x : nat) : (term175 x) = (term176 x).
Proof. exact (@lem4622707 (term106 x)). Qed.
Lemma lem4622709 (x : nat) (s : nat -> Prop) : (term177 x s) = (term105 x s).
Proof. exact (eq_refl (term177 x s)). Qed.
Lemma lem4622710 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4622711 (x : nat) (s : nat -> Prop) : (term178 x s) = (term172 x s).
Proof. exact (MK_COMB (@lem4622710) (@lem4622709 x s)). Qed.
Lemma lem4622712 (x : nat) (s : nat -> Prop) : (term178 x s) = (term171 x s).
Proof. exact (TRANS (@lem4622711 x s) (@lem4622706 x s)). Qed.
Lemma lem4622713 (x : nat) : (term179 x) = (term180 x).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4622712 x s)). Qed.
Lemma lem4622714 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem4622715 (x : nat) : (term176 x) = (term181 x).
Proof. exact (MK_COMB (@lem4622714) (@lem4622713 x)). Qed.
Lemma lem4622716 (x : nat) : (term175 x) = (term181 x).
Proof. exact (TRANS (@lem4622708 x) (@lem4622715 x)). Qed.
Lemma lem4622717 (P : nat -> Prop) : (term150 P) = (term151 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem4622718 : term113 = term182.
Proof. exact (@lem4622717 term108). Qed.
Lemma lem4622719 (x : nat) : (term183 x) = (term107 x).
Proof. exact (eq_refl (term183 x)). Qed.
Lemma lem4622720 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4622721 (x : nat) : (term184 x) = (term175 x).
Proof. exact (MK_COMB (@lem4622720) (@lem4622719 x)). Qed.
Lemma lem4622722 (x : nat) : (term184 x) = (term181 x).
Proof. exact (TRANS (@lem4622721 x) (@lem4622716 x)). Qed.
Lemma lem4622723 : term185 = term186.
Proof. exact (fun_ext (fun x : nat => @lem4622722 x)). Qed.
Lemma lem4622724 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4622725 : term182 = term187.
Proof. exact (MK_COMB (@lem4622724) (@lem4622723)). Qed.
Lemma lem4622726 : term113 = term187.
Proof. exact (TRANS (@lem4622718) (@lem4622725)). Qed.
Lemma lem4622885 {A : Type'} (P : A -> Prop) (Q : Prop) : (term188 A P Q) = (term189 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4622886 (P : nat -> Prop) (Q : Prop) : (term190 P Q) = (term191 P Q).
Proof. exact (@lem4622885 nat P Q). Qed.
Lemma lem4622887 (x : nat) (s : nat -> Prop) : (term192 x s) = (term193 x s).
Proof. exact (@lem4622886 (term144 s) (term50 x s)). Qed.
Lemma lem4622888 (s : nat -> Prop) (a : nat) : (term194 s a) = (term143 s a).
Proof. exact (eq_refl (term194 s a)). Qed.
Lemma lem4622889 (s : nat -> Prop) : (term195 s) = (term144 s).
Proof. exact (fun_ext (fun a : nat => @lem4622888 s a)). Qed.
Lemma lem4622890 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4622891 (s : nat -> Prop) : (term196 s) = (term145 s).
Proof. exact (MK_COMB (@lem4622890) (@lem4622889 s)). Qed.
Lemma lem4622892 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4622893 (s : nat -> Prop) : (term197 s) = (term146 s).
Proof. exact (MK_COMB (@lem4622892) (@lem4622891 s)). Qed.
Lemma lem4622894 (x : nat) (s : nat -> Prop) : (term50 x s) = (term50 x s).
Proof. exact (eq_refl (term50 x s)). Qed.
Lemma lem4622895 (x : nat) (s : nat -> Prop) : (term192 x s) = (term147 x s).
Proof. exact (MK_COMB (@lem4622893 s) (@lem4622894 x s)). Qed.
Lemma lem4622896 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4622897 (x : nat) (s : nat -> Prop) : (term198 x s) = (term199 x s).
Proof. exact (MK_COMB (@lem4622896) (@lem4622895 x s)). Qed.
Lemma lem4622898 (s : nat -> Prop) (a : nat) : (term194 s a) = (term143 s a).
Proof. exact (eq_refl (term194 s a)). Qed.
Lemma lem4622899 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4622900 (s : nat -> Prop) (a : nat) : (term200 s a) = (term201 s a).
Proof. exact (MK_COMB (@lem4622899) (@lem4622898 s a)). Qed.
Lemma lem4622901 (x : nat) (s : nat -> Prop) : (term50 x s) = (term50 x s).
Proof. exact (eq_refl (term50 x s)). Qed.
Lemma lem4622902 (a : nat) (x : nat) (s : nat -> Prop) : (term202 a x s) = (term203 a x s).
Proof. exact (MK_COMB (@lem4622900 s a) (@lem4622901 x s)). Qed.
Lemma lem4622903 (x : nat) (s : nat -> Prop) : (term204 x s) = (term205 x s).
Proof. exact (fun_ext (fun a : nat => @lem4622902 a x s)). Qed.
Lemma lem4622904 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4622905 (x : nat) (s : nat -> Prop) : (term193 x s) = (term206 x s).
Proof. exact (MK_COMB (@lem4622904) (@lem4622903 x s)). Qed.
Lemma lem4622906 (x : nat) (s : nat -> Prop) : ((term192 x s) = (term193 x s)) = ((term147 x s) = (term206 x s)).
Proof. exact (MK_COMB (@lem4622897 x s) (@lem4622905 x s)). Qed.
Lemma lem4622907 (x : nat) (s : nat -> Prop) : (term147 x s) = (term206 x s).
Proof. exact (EQ_MP (@lem4622906 x s) (@lem4622887 x s)). Qed.
Lemma lem4622908 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4622909 (x : nat) (s : nat -> Prop) : (term169 x s) = (term207 x s).
Proof. exact (MK_COMB (@lem4622908) (@lem4622907 x s)). Qed.
Lemma lem4622911 {A B : Type'} (P : type1413 A B) : (term208 A B P) = (term209 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4622912 (P : type1605) : (term210 P) = (term211 P).
Proof. exact (@lem4622911 nat nat P). Qed.
Lemma lem4622913 (x : nat) (s : nat -> Prop) : (term212 x s) = (term213 x s).
Proof. exact (@lem4622912 (term214 x s)). Qed.
Lemma lem4622914 (x : nat) (s : nat -> Prop) (a : nat) : (term215 x s a) = (term157 x s a).
Proof. exact (eq_refl (term215 x s a)). Qed.
Lemma lem4622915 (x' : nat) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem4622916 (x : nat) (s : nat -> Prop) (a : nat) (x' : nat) : (term216 x s a x') = (term217 x s a x').
Proof. exact (MK_COMB (@lem4622914 x s a) (@lem4622915 x')). Qed.
Lemma lem4622917 (x : nat) (s : nat -> Prop) (x' : nat) (a : nat) : (term217 x s a x') = (term149 x s x' a).
Proof. exact (eq_refl (term217 x s a x')). Qed.
Lemma lem4622918 (x : nat) (s : nat -> Prop) (x' : nat) (a : nat) : (term216 x s a x') = (term149 x s x' a).
Proof. exact (TRANS (@lem4622916 x s a x') (@lem4622917 x s x' a)). Qed.
Lemma lem4622919 (x : nat) (s : nat -> Prop) (a : nat) : (term218 x s a) = (term157 x s a).
Proof. exact (fun_ext (fun x' : nat => @lem4622918 x s x' a)). Qed.
Lemma lem4622920 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4622921 (x : nat) (s : nat -> Prop) (a : nat) : (term219 x s a) = (term158 x s a).
Proof. exact (MK_COMB (@lem4622920) (@lem4622919 x s a)). Qed.
Lemma lem4622922 (x : nat) (s : nat -> Prop) : (term220 x s) = (term166 x s).
Proof. exact (fun_ext (fun a : nat => @lem4622921 x s a)). Qed.
Lemma lem4622923 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4622924 (x : nat) (s : nat -> Prop) : (term212 x s) = (term167 x s).
Proof. exact (MK_COMB (@lem4622923) (@lem4622922 x s)). Qed.
Lemma lem4622925 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4622926 (x : nat) (s : nat -> Prop) : (term221 x s) = (term222 x s).
Proof. exact (MK_COMB (@lem4622925) (@lem4622924 x s)). Qed.
Lemma lem4622927 (x : nat) (s : nat -> Prop) (a : nat) : (term215 x s a) = (term157 x s a).
Proof. exact (eq_refl (term215 x s a)). Qed.
Lemma lem4622928 (x' : nat -> nat) (a : nat) : (x' a) = (x' a).
Proof. exact (eq_refl (x' a)). Qed.
Lemma lem4622929 (x : nat) (s : nat -> Prop) (x' : nat -> nat) (a : nat) : (term223 x s x' a) = (term224 x s x' a).
Proof. exact (MK_COMB (@lem4622927 x s a) (@lem4622928 x' a)). Qed.
Lemma lem4622930 (x : nat) (s : nat -> Prop) (x' : nat -> nat) (a : nat) : (term224 x s x' a) = (term225 x s x' a).
Proof. exact (eq_refl (term224 x s x' a)). Qed.
Lemma lem4622931 (x : nat) (s : nat -> Prop) (x' : nat -> nat) (a : nat) : (term223 x s x' a) = (term225 x s x' a).
Proof. exact (TRANS (@lem4622929 x s x' a) (@lem4622930 x s x' a)). Qed.
Lemma lem4622932 (x : nat) (s : nat -> Prop) (x' : nat -> nat) : (term226 x s x') = (term227 x s x').
Proof. exact (fun_ext (fun a : nat => @lem4622931 x s x' a)). Qed.
Lemma lem4622933 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4622934 (x : nat) (s : nat -> Prop) (x' : nat -> nat) : (term228 x s x') = (term229 x s x').
Proof. exact (MK_COMB (@lem4622933) (@lem4622932 x s x')). Qed.
Lemma lem4622935 (x : nat) (s : nat -> Prop) : (term230 x s) = (term231 x s).
Proof. exact (fun_ext (fun x' : nat -> nat => @lem4622934 x s x')). Qed.
Lemma lem4622936 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem4622937 (x : nat) (s : nat -> Prop) : (term213 x s) = (term232 x s).
Proof. exact (MK_COMB (@lem4622936) (@lem4622935 x s)). Qed.
Lemma lem4622938 (x : nat) (s : nat -> Prop) : ((term212 x s) = (term213 x s)) = ((term167 x s) = (term232 x s)).
Proof. exact (MK_COMB (@lem4622926 x s) (@lem4622937 x s)). Qed.
Lemma lem4622939 (x : nat) (s : nat -> Prop) : (term167 x s) = (term232 x s).
Proof. exact (EQ_MP (@lem4622938 x s) (@lem4622913 x s)). Qed.
Lemma lem4622940 (x : nat) (s : nat -> Prop) : (term171 x s) = (term233 x s).
Proof. exact (MK_COMB (@lem4622909 x s) (@lem4622939 x s)). Qed.
Lemma lem4622942 {A : Type'} (P : A -> Prop) (Q : Prop) : (term188 A P Q) = (term189 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4622943 (P : nat -> Prop) (Q : Prop) : (term190 P Q) = (term191 P Q).
Proof. exact (@lem4622942 nat P Q). Qed.
Lemma lem4622944 (x : nat) (s : nat -> Prop) : (term234 x s) = (term235 x s).
Proof. exact (@lem4622943 (term205 x s) (term232 x s)). Qed.
Lemma lem4622945 (a : nat) (x : nat) (s : nat -> Prop) : (term236 x s a) = (term203 a x s).
Proof. exact (eq_refl (term236 x s a)). Qed.
Lemma lem4622946 (x : nat) (s : nat -> Prop) : (term237 x s) = (term205 x s).
Proof. exact (fun_ext (fun a : nat => @lem4622945 a x s)). Qed.
Lemma lem4622947 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4622948 (x : nat) (s : nat -> Prop) : (term238 x s) = (term206 x s).
Proof. exact (MK_COMB (@lem4622947) (@lem4622946 x s)). Qed.
Lemma lem4622949 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4622950 (x : nat) (s : nat -> Prop) : (term239 x s) = (term207 x s).
Proof. exact (MK_COMB (@lem4622949) (@lem4622948 x s)). Qed.
Lemma lem4622951 (x : nat) (s : nat -> Prop) : (term232 x s) = (term232 x s).
Proof. exact (eq_refl (term232 x s)). Qed.
Lemma lem4622952 (x : nat) (s : nat -> Prop) : (term234 x s) = (term233 x s).
Proof. exact (MK_COMB (@lem4622950 x s) (@lem4622951 x s)). Qed.
Lemma lem4622953 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4622954 (x : nat) (s : nat -> Prop) : (term240 x s) = (term241 x s).
Proof. exact (MK_COMB (@lem4622953) (@lem4622952 x s)). Qed.
Lemma lem4622955 (a : nat) (x : nat) (s : nat -> Prop) : (term236 x s a) = (term203 a x s).
Proof. exact (eq_refl (term236 x s a)). Qed.
Lemma lem4622956 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4622957 (a : nat) (x : nat) (s : nat -> Prop) : (term242 x s a) = (term243 a x s).
Proof. exact (MK_COMB (@lem4622956) (@lem4622955 a x s)). Qed.
Lemma lem4622958 (x : nat) (s : nat -> Prop) : (term232 x s) = (term232 x s).
Proof. exact (eq_refl (term232 x s)). Qed.
Lemma lem4622959 (a : nat) (x : nat) (s : nat -> Prop) : (term244 a x s) = (term245 a x s).
Proof. exact (MK_COMB (@lem4622957 a x s) (@lem4622958 x s)). Qed.
Lemma lem4622960 (x : nat) (s : nat -> Prop) : (term246 x s) = (term247 x s).
Proof. exact (fun_ext (fun a : nat => @lem4622959 a x s)). Qed.
Lemma lem4622961 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4622962 (x : nat) (s : nat -> Prop) : (term235 x s) = (term248 x s).
Proof. exact (MK_COMB (@lem4622961) (@lem4622960 x s)). Qed.
Lemma lem4622963 (x : nat) (s : nat -> Prop) : ((term234 x s) = (term235 x s)) = ((term233 x s) = (term248 x s)).
Proof. exact (MK_COMB (@lem4622954 x s) (@lem4622962 x s)). Qed.
Lemma lem4622964 (x : nat) (s : nat -> Prop) : (term233 x s) = (term248 x s).
Proof. exact (EQ_MP (@lem4622963 x s) (@lem4622944 x s)). Qed.
Lemma lem4622966 {A : Type'} (P : Prop) (Q : A -> Prop) : (term249 A P Q) = (term250 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4622967 (P : Prop) (Q : type1002) : (term251 P Q) = (term252 P Q).
Proof. exact (@lem4622966 (nat -> nat) P Q). Qed.
Lemma lem4622968 (a : nat) (x : nat) (s : nat -> Prop) : (term253 a x s) = (term254 a x s).
Proof. exact (@lem4622967 (term203 a x s) (term231 x s)). Qed.
Lemma lem4622969 (x : nat) (s : nat -> Prop) (x' : nat -> nat) : (term255 x s x') = (term229 x s x').
Proof. exact (eq_refl (term255 x s x')). Qed.
Lemma lem4622970 (x : nat) (s : nat -> Prop) : (term256 x s) = (term231 x s).
Proof. exact (fun_ext (fun x' : nat -> nat => @lem4622969 x s x')). Qed.
Lemma lem4622971 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem4622972 (x : nat) (s : nat -> Prop) : (term257 x s) = (term232 x s).
Proof. exact (MK_COMB (@lem4622971) (@lem4622970 x s)). Qed.
Lemma lem4622973 (a : nat) (x : nat) (s : nat -> Prop) : (term243 a x s) = (term243 a x s).
Proof. exact (eq_refl (term243 a x s)). Qed.
Lemma lem4622974 (a : nat) (x : nat) (s : nat -> Prop) : (term253 a x s) = (term245 a x s).
Proof. exact (MK_COMB (@lem4622973 a x s) (@lem4622972 x s)). Qed.
Lemma lem4622975 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4622976 (a : nat) (x : nat) (s : nat -> Prop) : (term258 a x s) = (term259 a x s).
Proof. exact (MK_COMB (@lem4622975) (@lem4622974 a x s)). Qed.
Lemma lem4622977 (x : nat) (s : nat -> Prop) (x' : nat -> nat) : (term255 x s x') = (term229 x s x').
Proof. exact (eq_refl (term255 x s x')). Qed.
Lemma lem4622978 (a : nat) (x : nat) (s : nat -> Prop) : (term243 a x s) = (term243 a x s).
Proof. exact (eq_refl (term243 a x s)). Qed.
Lemma lem4622979 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) : (term260 a x s x') = (term261 a x s x').
Proof. exact (MK_COMB (@lem4622978 a x s) (@lem4622977 x s x')). Qed.
Lemma lem4622980 (a : nat) (x : nat) (s : nat -> Prop) : (term262 a x s) = (term263 a x s).
Proof. exact (fun_ext (fun x' : nat -> nat => @lem4622979 a x s x')). Qed.
Lemma lem4622981 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem4622982 (a : nat) (x : nat) (s : nat -> Prop) : (term254 a x s) = (term264 a x s).
Proof. exact (MK_COMB (@lem4622981) (@lem4622980 a x s)). Qed.
Lemma lem4622983 (a : nat) (x : nat) (s : nat -> Prop) : ((term253 a x s) = (term254 a x s)) = ((term245 a x s) = (term264 a x s)).
Proof. exact (MK_COMB (@lem4622976 a x s) (@lem4622982 a x s)). Qed.
Lemma lem4622984 (a : nat) (x : nat) (s : nat -> Prop) : (term245 a x s) = (term264 a x s).
Proof. exact (EQ_MP (@lem4622983 a x s) (@lem4622968 a x s)). Qed.
Lemma lem4622985 (x : nat) (s : nat -> Prop) : (term247 x s) = (term265 x s).
Proof. exact (fun_ext (fun a : nat => @lem4622984 a x s)). Qed.
Lemma lem4622986 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4622987 (x : nat) (s : nat -> Prop) : (term248 x s) = (term266 x s).
Proof. exact (MK_COMB (@lem4622986) (@lem4622985 x s)). Qed.
Lemma lem4622988 (x : nat) (s : nat -> Prop) : (term233 x s) = (term266 x s).
Proof. exact (TRANS (@lem4622964 x s) (@lem4622987 x s)). Qed.
Lemma lem4622989 (x : nat) (s : nat -> Prop) : (term171 x s) = (term266 x s).
Proof. exact (TRANS (@lem4622940 x s) (@lem4622988 x s)). Qed.
Lemma lem4622990 (x : nat) : (term180 x) = (term267 x).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem4622989 x s)). Qed.
Lemma lem4622991 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem4622992 (x : nat) : (term181 x) = (term268 x).
Proof. exact (MK_COMB (@lem4622991) (@lem4622990 x)). Qed.
Lemma lem4622993 : term186 = term269.
Proof. exact (fun_ext (fun x : nat => @lem4622992 x)). Qed.
Lemma lem4622994 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4622996 : term187 = term270.
Proof. exact (MK_COMB (@lem4622994) (@lem4622993)). Qed.
Lemma lem4622997 : term113 = term270.
Proof. exact (TRANS (@lem4622726) (@lem4622996)). Qed.
Lemma lem4622998 (h1 : term113) : term270.
Proof. exact (EQ_MP (@lem4622997) (@lem4622647 h1)). Qed.
Lemma lem4623005 (m : nat) (n : nat) (p : nat) : (term271 m n p) = (term272 m n p).
Proof. exact (@lem17045 (Peano.le m n) (Peano.le n p)). Qed.
Lemma lem4623006 (m : nat) (p : nat) : (Peano.le m p) = (Peano.le m p).
Proof. exact (eq_refl (Peano.le m p)). Qed.
Lemma lem4623007 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4623008 (m : nat) (n : nat) (p : nat) : (term273 m n p) = (term274 m n p).
Proof. exact (MK_COMB (@lem4623007) (@lem4623005 m n p)). Qed.
Lemma lem4623009 (n : nat) (m : nat) (p : nat) : (term275 n m p) = (term276 n m p).
Proof. exact (MK_COMB (@lem4623008 m n p) (@lem4623006 m p)). Qed.
Lemma lem4623010 (n : nat) (m : nat) (p : nat) : (term130 n m p) = (term275 n m p).
Proof. exact (@lem17265 (term277 m n p) (Peano.le m p)). Qed.
Lemma lem4623011 (n : nat) (m : nat) (p : nat) : (term130 n m p) = (term276 n m p).
Proof. exact (TRANS (@lem4623010 n m p) (@lem4623009 n m p)). Qed.
Lemma lem4623012 (n : nat) (m : nat) : (term131 n m) = (term278 n m).
Proof. exact (fun_ext (fun p : nat => @lem4623011 n m p)). Qed.
Lemma lem4623013 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4623014 (n : nat) (m : nat) : (term132 n m) = (term279 n m).
Proof. exact (MK_COMB (@lem4623013) (@lem4623012 n m)). Qed.
Lemma lem4623015 (m : nat) : (term133 m) = (term280 m).
Proof. exact (fun_ext (fun n : nat => @lem4623014 n m)). Qed.
Lemma lem4623016 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4623017 (m : nat) : (term134 m) = (term281 m).
Proof. exact (MK_COMB (@lem4623016) (@lem4623015 m)). Qed.
Lemma lem4623018 : term135 = term282.
Proof. exact (fun_ext (fun m : nat => @lem4623017 m)). Qed.
Lemma lem4623019 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4623080 : term136 = term283.
Proof. exact (MK_COMB (@lem4623019) (@lem4623018)). Qed.
Lemma lem4623081 (h1 : term136) : term283.
Proof. exact (EQ_MP (@lem4623080) (@lem4622648 h1)). Qed.
Lemma lem4623086 (n : nat) (m : nat) : (term126 n m) = (term126 n m).
Proof. exact (eq_refl (term126 n m)). Qed.
Lemma lem4623087 (m : nat) : (term127 m) = (term127 m).
Proof. exact (fun_ext (fun n : nat => @lem4623086 n m)). Qed.
Lemma lem4623088 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4623089 (m : nat) : (term128 m) = (term128 m).
Proof. exact (MK_COMB (@lem4623088) (@lem4623087 m)). Qed.
Lemma lem4623090 : term129 = term129.
Proof. exact (fun_ext (fun m : nat => @lem4623089 m)). Qed.
Lemma lem4623091 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4623148 : term120 = term120.
Proof. exact (MK_COMB (@lem4623091) (@lem4623090)). Qed.
Lemma lem4623149 (h1 : term120) : term120.
Proof. exact (EQ_MP (@lem4623148) (@lem4622649 h1)). Qed.
Lemma lem4623150 (x : nat) (h1 : term268 x) : term268 x.
Proof. exact (h1). Qed.
Lemma lem4623151 (x : nat) (s : nat -> Prop) (h1 : term266 x s) : term266 x s.
Proof. exact (h1). Qed.
Lemma lem4623152 (a : nat) (x : nat) (s : nat -> Prop) (h1 : term264 a x s) : term264 a x s.
Proof. exact (h1). Qed.
Lemma lem4623153 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term261 a x s x'.
Proof. exact (h1). Qed.
Lemma lem4623178 (n : nat) (m : nat) (p : nat) : (term276 n m p) = (term276 n m p).
Proof. exact (eq_refl (term276 n m p)). Qed.
Lemma lem4623179 (n : nat) (m : nat) : (term278 n m) = (term278 n m).
Proof. exact (fun_ext (fun p : nat => @lem4623178 n m p)). Qed.
Lemma lem4623180 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4623181 (n : nat) (m : nat) : (term279 n m) = (term279 n m).
Proof. exact (MK_COMB (@lem4623180) (@lem4623179 n m)). Qed.
Lemma lem4623182 (m : nat) : (term280 m) = (term280 m).
Proof. exact (fun_ext (fun n : nat => @lem4623181 n m)). Qed.
Lemma lem4623183 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4623184 (m : nat) : (term281 m) = (term281 m).
Proof. exact (MK_COMB (@lem4623183) (@lem4623182 m)). Qed.
Lemma lem4623185 : term282 = term282.
Proof. exact (fun_ext (fun m : nat => @lem4623184 m)). Qed.
Lemma lem4623186 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4623187 : term283 = term283.
Proof. exact (MK_COMB (@lem4623186) (@lem4623185)). Qed.
Lemma lem4623188 (h1 : term136) : term283.
Proof. exact (EQ_MP (@lem4623187) (@lem4623081 h1)). Qed.
Lemma lem4623201 (n : nat) (m : nat) : (term126 n m) = (term126 n m).
Proof. exact (eq_refl (term126 n m)). Qed.
Lemma lem4623202 (m : nat) : (term127 m) = (term127 m).
Proof. exact (fun_ext (fun n : nat => @lem4623201 n m)). Qed.
Lemma lem4623203 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4623204 (m : nat) : (term128 m) = (term128 m).
Proof. exact (MK_COMB (@lem4623203) (@lem4623202 m)). Qed.
Lemma lem4623205 : term129 = term129.
Proof. exact (fun_ext (fun m : nat => @lem4623204 m)). Qed.
Lemma lem4623206 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4623207 : term120 = term120.
Proof. exact (MK_COMB (@lem4623206) (@lem4623205)). Qed.
Lemma lem4623208 (h1 : term120) : term120.
Proof. exact (EQ_MP (@lem4623207) (@lem4623149 h1)). Qed.
Lemma lem4623237 (x : nat) (s : nat -> Prop) (x' : nat -> nat) (a : nat) : (term225 x s x' a) = (term225 x s x' a).
Proof. exact (eq_refl (term225 x s x' a)). Qed.
Lemma lem4623238 (x : nat) (s : nat -> Prop) (x' : nat -> nat) : (term227 x s x') = (term227 x s x').
Proof. exact (fun_ext (fun a : nat => @lem4623237 x s x' a)). Qed.
Lemma lem4623239 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4623240 (x : nat) (s : nat -> Prop) (x' : nat -> nat) : (term229 x s x') = (term229 x s x').
Proof. exact (MK_COMB (@lem4623239) (@lem4623238 x s x')). Qed.
Lemma lem4623253 (x : nat) (s : nat -> Prop) : (term50 x s) = (term50 x s).
Proof. exact (eq_refl (term50 x s)). Qed.
Lemma lem4623268 (s : nat -> Prop) (x : nat) (a : nat) : (term141 s x a) = (term141 s x a).
Proof. exact (eq_refl (term141 s x a)). Qed.
Lemma lem4623269 (s : nat -> Prop) (a : nat) : (term142 s a) = (term142 s a).
Proof. exact (fun_ext (fun x : nat => @lem4623268 s x a)). Qed.
Lemma lem4623270 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4623271 (s : nat -> Prop) (a : nat) : (term143 s a) = (term143 s a).
Proof. exact (MK_COMB (@lem4623270) (@lem4623269 s a)). Qed.
Lemma lem4623272 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4623273 (s : nat -> Prop) (a : nat) : (term201 s a) = (term201 s a).
Proof. exact (MK_COMB (@lem4623272) (@lem4623271 s a)). Qed.
Lemma lem4623274 (a : nat) (x : nat) (s : nat -> Prop) : (term203 a x s) = (term203 a x s).
Proof. exact (MK_COMB (@lem4623273 s a) (@lem4623253 x s)). Qed.
Lemma lem4623275 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4623276 (a : nat) (x : nat) (s : nat -> Prop) : (term243 a x s) = (term243 a x s).
Proof. exact (MK_COMB (@lem4623275) (@lem4623274 a x s)). Qed.
Lemma lem4623277 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) : (term261 a x s x') = (term261 a x s x').
Proof. exact (MK_COMB (@lem4623276 a x s) (@lem4623240 x s x')). Qed.
Lemma lem4623278 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term261 a x s x'.
Proof. exact (EQ_MP (@lem4623277 a x s x') (@lem4623153 a x s x' h1)). Qed.
Lemma lem4623279 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term229 x s x'.
Proof. exact (proj2 (@lem4623278 a x s x' h1)). Qed.
Lemma lem4623280 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term203 a x s.
Proof. exact (proj1 (@lem4623278 a x s x' h1)). Qed.
Lemma lem4623282 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term143 s a.
Proof. exact (proj1 (@lem4623280 a x s x' h1)). Qed.
Lemma lem4623298 (n : nat) (m : nat) (p : nat) : (term276 n m p) = (term276 n m p).
Proof. exact (eq_refl (term276 n m p)). Qed.
Lemma lem4623299 (n : nat) (m : nat) : (term278 n m) = (term278 n m).
Proof. exact (fun_ext (fun p : nat => @lem4623298 n m p)). Qed.
Lemma lem4623300 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4623301 (n : nat) (m : nat) : (term279 n m) = (term279 n m).
Proof. exact (MK_COMB (@lem4623300) (@lem4623299 n m)). Qed.
Lemma lem4623302 (m : nat) : (term280 m) = (term280 m).
Proof. exact (fun_ext (fun n : nat => @lem4623301 n m)). Qed.
Lemma lem4623303 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4623304 (m : nat) : (term281 m) = (term281 m).
Proof. exact (MK_COMB (@lem4623303) (@lem4623302 m)). Qed.
Lemma lem4623305 : term282 = term282.
Proof. exact (fun_ext (fun m : nat => @lem4623304 m)). Qed.
Lemma lem4623306 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4623308 : term283 = term283.
Proof. exact (MK_COMB (@lem4623306) (@lem4623305)). Qed.
Lemma lem4623309 (h1 : term136) : term283.
Proof. exact (EQ_MP (@lem4623308) (@lem4623188 h1)). Qed.
Lemma lem4623317 (n : nat) (m : nat) : (term126 n m) = (term126 n m).
Proof. exact (eq_refl (term126 n m)). Qed.
Lemma lem4623318 (m : nat) : (term127 m) = (term127 m).
Proof. exact (fun_ext (fun n : nat => @lem4623317 n m)). Qed.
Lemma lem4623319 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4623320 (m : nat) : (term128 m) = (term128 m).
Proof. exact (MK_COMB (@lem4623319) (@lem4623318 m)). Qed.
Lemma lem4623321 : term129 = term129.
Proof. exact (fun_ext (fun m : nat => @lem4623320 m)). Qed.
Lemma lem4623322 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4623324 : term120 = term120.
Proof. exact (MK_COMB (@lem4623322) (@lem4623321)). Qed.
Lemma lem4623325 (h1 : term120) : term120.
Proof. exact (EQ_MP (@lem4623324) (@lem4623208 h1)). Qed.
Lemma lem4623337 (x : nat) (s : nat -> Prop) (x' : nat -> nat) (a : nat) : (term225 x s x' a) = (term225 x s x' a).
Proof. exact (eq_refl (term225 x s x' a)). Qed.
Lemma lem4623338 (x : nat) (s : nat -> Prop) (x' : nat -> nat) : (term227 x s x') = (term227 x s x').
Proof. exact (fun_ext (fun a : nat => @lem4623337 x s x' a)). Qed.
Lemma lem4623339 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4623341 (x : nat) (s : nat -> Prop) (x' : nat -> nat) : (term229 x s x') = (term229 x s x').
Proof. exact (MK_COMB (@lem4623339) (@lem4623338 x s x')). Qed.
Lemma lem4623342 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term229 x s x'.
Proof. exact (EQ_MP (@lem4623341 x s x') (@lem4623279 a x s x' h1)). Qed.
Lemma lem4623350 (s : nat -> Prop) (x : nat) (a : nat) : (term141 s x a) = (term141 s x a).
Proof. exact (eq_refl (term141 s x a)). Qed.
Lemma lem4623351 (s : nat -> Prop) (a : nat) : (term142 s a) = (term142 s a).
Proof. exact (fun_ext (fun x : nat => @lem4623350 s x a)). Qed.
Lemma lem4623352 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4623354 (s : nat -> Prop) (a : nat) : (term143 s a) = (term143 s a).
Proof. exact (MK_COMB (@lem4623352) (@lem4623351 s a)). Qed.
Lemma lem4623355 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term143 s a.
Proof. exact (EQ_MP (@lem4623354 s a) (@lem4623282 a x s x' h1)). Qed.
Lemma lem4623364 (_55518 : nat) (h1 : term136) : term284 _55518.
Proof. exact (@lem4623309 h1 _55518). Qed.
Lemma lem4623365 (_55518 : nat) : (term284 _55518) = (term281 _55518).
Proof. exact (eq_refl (term284 _55518)). Qed.
Lemma lem4623366 (_55518 : nat) (h1 : term136) : term281 _55518.
Proof. exact (EQ_MP (@lem4623365 _55518) (@lem4623364 _55518 h1)). Qed.
Lemma lem4623367 (_55518 : nat) (_55519 : nat) (h1 : term136) : term285 _55518 _55519.
Proof. exact (@lem4623366 _55518 h1 _55519). Qed.
Lemma lem4623368 (_55519 : nat) (_55518 : nat) : (term285 _55518 _55519) = (term279 _55519 _55518).
Proof. exact (eq_refl (term285 _55518 _55519)). Qed.
Lemma lem4623369 (_55519 : nat) (_55518 : nat) (h1 : term136) : term279 _55519 _55518.
Proof. exact (EQ_MP (@lem4623368 _55519 _55518) (@lem4623367 _55518 _55519 h1)). Qed.
Lemma lem4623370 (_55519 : nat) (_55518 : nat) (_55520 : nat) (h1 : term136) : term286 _55519 _55518 _55520.
Proof. exact (@lem4623369 _55519 _55518 h1 _55520). Qed.
Lemma lem4623371 (_55519 : nat) (_55518 : nat) (_55520 : nat) : (term286 _55519 _55518 _55520) = (term276 _55519 _55518 _55520).
Proof. exact (eq_refl (term286 _55519 _55518 _55520)). Qed.
Lemma lem4623372 (_55519 : nat) (_55518 : nat) (_55520 : nat) (h1 : term136) : term276 _55519 _55518 _55520.
Proof. exact (EQ_MP (@lem4623371 _55519 _55518 _55520) (@lem4623370 _55519 _55518 _55520 h1)). Qed.
Lemma lem4623373 (_55521 : nat) (h1 : term120) : term287 _55521.
Proof. exact (@lem4623325 h1 _55521). Qed.
Lemma lem4623374 (_55521 : nat) : (term287 _55521) = (term128 _55521).
Proof. exact (eq_refl (term287 _55521)). Qed.
Lemma lem4623375 (_55521 : nat) (h1 : term120) : term128 _55521.
Proof. exact (EQ_MP (@lem4623374 _55521) (@lem4623373 _55521 h1)). Qed.
Lemma lem4623376 (_55521 : nat) (_55522 : nat) (h1 : term120) : term288 _55521 _55522.
Proof. exact (@lem4623375 _55521 h1 _55522). Qed.
Lemma lem4623377 (_55522 : nat) (_55521 : nat) : (term288 _55521 _55522) = (term126 _55522 _55521).
Proof. exact (eq_refl (term288 _55521 _55522)). Qed.
Lemma lem4623379 (_55523 : nat) (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term289 x s x' _55523.
Proof. exact (@lem4623342 a x s x' h1 _55523). Qed.
Lemma lem4623380 (x : nat) (s : nat -> Prop) (x' : nat -> nat) (_55523 : nat) : (term289 x s x' _55523) = (term225 x s x' _55523).
Proof. exact (eq_refl (term289 x s x' _55523)). Qed.
Lemma lem4623381 (_55523 : nat) (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term225 x s x' _55523.
Proof. exact (EQ_MP (@lem4623380 x s x' _55523) (@lem4623379 _55523 a x s x' h1)). Qed.
Lemma lem4623382 (_55524 : nat) (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term290 s a _55524.
Proof. exact (@lem4623355 a x s x' h1 _55524). Qed.
Lemma lem4623383 (s : nat -> Prop) (_55524 : nat) (a : nat) : (term290 s a _55524) = (term141 s _55524 a).
Proof. exact (eq_refl (term290 s a _55524)). Qed.
Lemma lem4623397 (_55519 : nat) (_55518 : nat) (_55520 : nat) : (term276 _55519 _55518 _55520) = (term291 _55519 _55518 _55520).
Proof. exact (@lem4622097 (term292 _55518 _55519) (term292 _55519 _55520) (Peano.le _55518 _55520)). Qed.
Lemma lem4623398 (_55519 : nat) (_55518 : nat) (_55520 : nat) (h1 : term136) : term291 _55519 _55518 _55520.
Proof. exact (EQ_MP (@lem4623397 _55519 _55518 _55520) (@lem4623372 _55519 _55518 _55520 h1)). Qed.
Lemma lem4623404 (_55522 : nat) (_55521 : nat) (h1 : term120) : term126 _55522 _55521.
Proof. exact (EQ_MP (@lem4623377 _55522 _55521) (@lem4623376 _55521 _55522 h1)). Qed.
Lemma lem4623410 (_55524 : nat) (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term141 s _55524 a.
Proof. exact (EQ_MP (@lem4623383 s _55524 a) (@lem4623382 _55524 a x s x' h1)). Qed.
Lemma lem4623420 (_55523 : nat) (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term293 x x' _55523 s.
Proof. exact (proj1 (@lem4623381 _55523 a x s x' h1)). Qed.
Lemma lem4623422 (_55523 : nat) (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term294 x' _55523.
Proof. exact (proj2 (@lem4623381 _55523 a x s x' h1)). Qed.
Lemma lem4623454 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem4623455 (_55531 : nat) (_55533 : nat) (h1 : _55531 = _55533) : _55531 = _55533.
Proof. exact (h1). Qed.
Lemma lem4623456 (_55532 : nat) (_55534 : nat) (h1 : _55532 = _55534) : _55532 = _55534.
Proof. exact (h1). Qed.
Lemma lem4623457 (_55531 : nat) (_55533 : nat) (h1 : _55531 = _55533) : (Peano.le _55531) = (Peano.le _55533).
Proof. exact (MK_COMB (@lem4623454) (@lem4623455 _55531 _55533 h1)). Qed.
Lemma lem4623458 (_55531 : nat) (_55533 : nat) (_55532 : nat) (_55534 : nat) (h1 : _55531 = _55533) (h2 : _55532 = _55534) : (Peano.le _55531 _55532) = (Peano.le _55533 _55534).
Proof. exact (MK_COMB (@lem4623457 _55531 _55533 h1) (@lem4623456 _55532 _55534 h2)). Qed.
Lemma lem4623460 (b : Prop) (a : Prop) : term295 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem4623461 (_55533 : nat) (_55534 : nat) (_55531 : nat) (_55532 : nat) : term296 _55533 _55534 _55531 _55532.
Proof. exact (@lem4623460 (Peano.le _55533 _55534) (Peano.le _55531 _55532)). Qed.
Lemma lem4623462 (_55531 : nat) (_55533 : nat) (_55532 : nat) (_55534 : nat) (h1 : _55531 = _55533) (h2 : _55532 = _55534) : term297 _55533 _55534 _55531 _55532.
Proof. exact (@lem4623461 _55533 _55534 _55531 _55532 (@lem4623458 _55531 _55533 _55532 _55534 h1 h2)). Qed.
Lemma lem4623463 (_55534 : nat) (_55532 : nat) (_55531 : nat) (_55533 : nat) (h1 : _55531 = _55533) : term298 _55533 _55534 _55531 _55532.
Proof. exact (fun h0 : _55532 = _55534 => @lem4623462 _55531 _55533 _55532 _55534 h1 h0). Qed.
Lemma lem4623465 (a : Prop) (b : Prop) : (a -> b) = (term299 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem4623466 (_55533 : nat) (_55534 : nat) (_55531 : nat) (_55532 : nat) : (term298 _55533 _55534 _55531 _55532) = (term300 _55533 _55534 _55531 _55532).
Proof. exact (@lem4623465 (_55532 = _55534) (term297 _55533 _55534 _55531 _55532)). Qed.
Lemma lem4623467 (_55534 : nat) (_55532 : nat) (_55531 : nat) (_55533 : nat) (h1 : _55531 = _55533) : term300 _55533 _55534 _55531 _55532.
Proof. exact (EQ_MP (@lem4623466 _55533 _55534 _55531 _55532) (@lem4623463 _55534 _55532 _55531 _55533 h1)). Qed.
Lemma lem4623468 (_55533 : nat) (_55534 : nat) (_55531 : nat) (_55532 : nat) : term301 _55533 _55534 _55531 _55532.
Proof. exact (fun h0 : _55531 = _55533 => @lem4623467 _55534 _55532 _55531 _55533 h0). Qed.
Lemma lem4623470 (a : Prop) (b : Prop) : (a -> b) = (term299 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem4623471 (_55533 : nat) (_55534 : nat) (_55531 : nat) (_55532 : nat) : (term301 _55533 _55534 _55531 _55532) = (term302 _55533 _55534 _55531 _55532).
Proof. exact (@lem4623470 (_55531 = _55533) (term300 _55533 _55534 _55531 _55532)). Qed.
Lemma lem4623472 (_55533 : nat) (_55534 : nat) (_55531 : nat) (_55532 : nat) : term302 _55533 _55534 _55531 _55532.
Proof. exact (EQ_MP (@lem4623471 _55533 _55534 _55531 _55532) (@lem4623468 _55533 _55534 _55531 _55532)). Qed.
Lemma lem4623473 (x' : nat -> nat) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem4623474 (_55535 : nat) (_55536 : nat) (h1 : _55535 = _55536) : _55535 = _55536.
Proof. exact (h1). Qed.
Lemma lem4623475 (x' : nat -> nat) (_55535 : nat) (_55536 : nat) (h1 : _55535 = _55536) : (x' _55535) = (x' _55536).
Proof. exact (MK_COMB (@lem4623473 x') (@lem4623474 _55535 _55536 h1)). Qed.
Lemma lem4623476 (_55535 : nat) (x' : nat -> nat) (_55536 : nat) : term303 _55535 x' _55536.
Proof. exact (fun h0 : _55535 = _55536 => @lem4623475 x' _55535 _55536 h0). Qed.
Lemma lem4623478 (a : Prop) (b : Prop) : (a -> b) = (term299 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem4623479 (_55535 : nat) (x' : nat -> nat) (_55536 : nat) : (term303 _55535 x' _55536) = (term304 _55535 x' _55536).
Proof. exact (@lem4623478 (_55535 = _55536) ((x' _55535) = (x' _55536))). Qed.
Lemma lem4623480 (_55535 : nat) (x' : nat -> nat) (_55536 : nat) : term304 _55535 x' _55536.
Proof. exact (EQ_MP (@lem4623479 _55535 x' _55536) (@lem4623476 _55535 x' _55536)). Qed.
Lemma lem4623486 (_55523 : nat) (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term294 x' _55523.
Proof. exact (proj2 (@lem4623381 _55523 a x s x' h1)). Qed.
Lemma lem4623487 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term305 x' a.
Proof. exact (@lem4623486 (x' a) a x s x' h1). Qed.
Lemma lem4623488 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term306 x' a.
Proof. exact (fun h0 : term307 x' a => @lem4623487 a x s x' h1). Qed.
Lemma lem4623490 (p : Prop) : (term308 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4623491 (x' : nat -> nat) (a : nat) : (term306 x' a) = (term305 x' a).
Proof. exact (@lem4623490 (term307 x' a)). Qed.
Lemma lem4623492 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term305 x' a.
Proof. exact (EQ_MP (@lem4623491 x' a) (@lem4623488 a x s x' h1)). Qed.
Lemma lem4623503 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4623504 (_55522 : nat) (_55521 : nat) : (term126 _55521 _55522) = (term126 _55522 _55521).
Proof. exact (@lem4623503 (Peano.le _55521 _55522) (Peano.le _55522 _55521)). Qed.
Lemma lem4623510 (_55522 : nat) (_55521 : nat) : (term309 _55522 _55521) = (term309 _55522 _55521).
Proof. exact (eq_refl (term309 _55522 _55521)). Qed.
Lemma lem4623511 (_55522 : nat) (_55521 : nat) : ((term126 _55522 _55521) = (term126 _55521 _55522)) = ((term126 _55522 _55521) = (term126 _55522 _55521)).
Proof. exact (MK_COMB (@lem4623510 _55522 _55521) (@lem4623504 _55522 _55521)). Qed.
Lemma lem4623513 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4623514 (x : Prop) : (x = x) = True.
Proof. exact (@lem4623513 Prop x). Qed.
Lemma lem4623515 (_55522 : nat) (_55521 : nat) : ((term126 _55522 _55521) = (term126 _55522 _55521)) = True.
Proof. exact (@lem4623514 (term126 _55522 _55521)). Qed.
Lemma lem4623516 (_55521 : nat) (_55522 : nat) : ((term126 _55522 _55521) = (term126 _55521 _55522)) = True.
Proof. exact (TRANS (@lem4623511 _55522 _55521) (@lem4623515 _55522 _55521)). Qed.
Lemma lem4623517 (_55521 : nat) (_55522 : nat) : True = ((term126 _55522 _55521) = (term126 _55521 _55522)).
Proof. exact (SYM (@lem4623516 _55521 _55522)). Qed.
Lemma lem4623518 (_55521 : nat) (_55522 : nat) : (term126 _55522 _55521) = (term126 _55521 _55522).
Proof. exact (EQ_MP (@lem4623517 _55521 _55522) (@lem0)). Qed.
Lemma lem4623519 (_55521 : nat) (_55522 : nat) (h1 : term120) : term126 _55521 _55522.
Proof. exact (EQ_MP (@lem4623518 _55521 _55522) (@lem4623404 _55522 _55521 h1)). Qed.
Lemma lem4623521 (b : Prop) (a : Prop) : (a \/ b) = (term310 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4623524 (_55522 : nat) (_55521 : nat) : (term126 _55521 _55522) = (term311 _55522 _55521).
Proof. exact (@lem4623521 (Peano.le _55521 _55522) (Peano.le _55522 _55521)). Qed.
Lemma lem4623527 (_55522 : nat) (_55521 : nat) (h1 : term120) : term311 _55522 _55521.
Proof. exact (EQ_MP (@lem4623524 _55522 _55521) (@lem4623519 _55521 _55522 h1)). Qed.
Lemma lem4623528 (x' : nat -> nat) (a : nat) (h1 : term120) : term312 x' a.
Proof. exact (@lem4623527 (x' a) (term313 x' a) h1). Qed.
Lemma lem4623531 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term120) (h2 : term261 a x s x') : term314 x' a.
Proof. exact (@lem4623528 x' a h1 (@lem4623492 a x s x' h2)). Qed.
Lemma lem4623532 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term120) (h2 : term261 a x s x') : term315 x' a.
Proof. exact (fun h0 : term316 x' a => @lem4623531 a x s x' h1 h2). Qed.
Lemma lem4623534 (p : Prop) : (term317 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4623535 (x' : nat -> nat) (a : nat) : (term315 x' a) = (term314 x' a).
Proof. exact (@lem4623534 (term314 x' a)). Qed.
Lemma lem4623536 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term120) (h2 : term261 a x s x') : term314 x' a.
Proof. exact (EQ_MP (@lem4623535 x' a) (@lem4623532 a x s x' h1 h2)). Qed.
Lemma lem4623539 (x' : nat -> nat) (a : nat) (h1 : term294 x' a) : term294 x' a.
Proof. exact (h1). Qed.
Lemma lem4623540 (x' : nat -> nat) (a : nat) (h1 : term294 x' a) : term318 x' a.
Proof. exact (fun h0 : term319 x' a => @lem4623539 x' a h1). Qed.
Lemma lem4623542 (p : Prop) : (term308 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4623543 (x' : nat -> nat) (a : nat) : (term318 x' a) = (term294 x' a).
Proof. exact (@lem4623542 (term319 x' a)). Qed.
Lemma lem4623544 (x' : nat -> nat) (a : nat) (h1 : term294 x' a) : term294 x' a.
Proof. exact (EQ_MP (@lem4623543 x' a) (@lem4623540 x' a h1)). Qed.
Lemma lem4623560 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4623561 (_55518 : nat) (_55519 : nat) (_55520 : nat) : (term320 _55519 _55518 _55520) = (term321 _55518 _55519 _55520).
Proof. exact (@lem4623560 (Peano.le _55518 _55520) (term292 _55519 _55520)). Qed.
Lemma lem4623567 (_55518 : nat) (_55519 : nat) : (term322 _55518 _55519) = (term322 _55518 _55519).
Proof. exact (eq_refl (term322 _55518 _55519)). Qed.
Lemma lem4623568 (_55518 : nat) (_55519 : nat) (_55520 : nat) : (term291 _55519 _55518 _55520) = (term323 _55518 _55519 _55520).
Proof. exact (MK_COMB (@lem4623567 _55518 _55519) (@lem4623561 _55518 _55519 _55520)). Qed.
Lemma lem4623572 (q : Prop) (p : Prop) (r : Prop) : (term20 p q r) = (term20 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4623573 (_55518 : nat) (_55519 : nat) (_55520 : nat) : (term323 _55518 _55519 _55520) = (term324 _55518 _55519 _55520).
Proof. exact (@lem4623572 (Peano.le _55518 _55520) (term292 _55518 _55519) (term292 _55519 _55520)). Qed.
Lemma lem4623589 (_55518 : nat) (_55519 : nat) (_55520 : nat) : (term291 _55519 _55518 _55520) = (term324 _55518 _55519 _55520).
Proof. exact (TRANS (@lem4623568 _55518 _55519 _55520) (@lem4623573 _55518 _55519 _55520)). Qed.
Lemma lem4623590 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4623591 (_55518 : nat) (_55519 : nat) (_55520 : nat) : (term325 _55519 _55518 _55520) = (term326 _55518 _55519 _55520).
Proof. exact (MK_COMB (@lem4623590) (@lem4623589 _55518 _55519 _55520)). Qed.
Lemma lem4623595 (q : Prop) (p : Prop) (r : Prop) : (term20 p q r) = (term20 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4623596 (_55519 : nat) (_55518 : nat) (_55520 : nat) : (term327 _55519 _55518 _55520) = (term291 _55519 _55518 _55520).
Proof. exact (@lem4623595 (term292 _55518 _55519) (term292 _55519 _55520) (Peano.le _55518 _55520)). Qed.
Lemma lem4623610 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4623611 (_55518 : nat) (_55519 : nat) (_55520 : nat) : (term320 _55519 _55518 _55520) = (term321 _55518 _55519 _55520).
Proof. exact (@lem4623610 (Peano.le _55518 _55520) (term292 _55519 _55520)). Qed.
Lemma lem4623617 (_55518 : nat) (_55519 : nat) : (term322 _55518 _55519) = (term322 _55518 _55519).
Proof. exact (eq_refl (term322 _55518 _55519)). Qed.
Lemma lem4623618 (_55518 : nat) (_55519 : nat) (_55520 : nat) : (term291 _55519 _55518 _55520) = (term323 _55518 _55519 _55520).
Proof. exact (MK_COMB (@lem4623617 _55518 _55519) (@lem4623611 _55518 _55519 _55520)). Qed.
Lemma lem4623622 (q : Prop) (p : Prop) (r : Prop) : (term20 p q r) = (term20 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4623623 (_55518 : nat) (_55519 : nat) (_55520 : nat) : (term323 _55518 _55519 _55520) = (term324 _55518 _55519 _55520).
Proof. exact (@lem4623622 (Peano.le _55518 _55520) (term292 _55518 _55519) (term292 _55519 _55520)). Qed.
Lemma lem4623639 (_55518 : nat) (_55519 : nat) (_55520 : nat) : (term291 _55519 _55518 _55520) = (term324 _55518 _55519 _55520).
Proof. exact (TRANS (@lem4623618 _55518 _55519 _55520) (@lem4623623 _55518 _55519 _55520)). Qed.
Lemma lem4623640 (_55518 : nat) (_55519 : nat) (_55520 : nat) : (term327 _55519 _55518 _55520) = (term324 _55518 _55519 _55520).
Proof. exact (TRANS (@lem4623596 _55519 _55518 _55520) (@lem4623639 _55518 _55519 _55520)). Qed.
Lemma lem4623641 (_55518 : nat) (_55519 : nat) (_55520 : nat) : ((term291 _55519 _55518 _55520) = (term327 _55519 _55518 _55520)) = ((term324 _55518 _55519 _55520) = (term324 _55518 _55519 _55520)).
Proof. exact (MK_COMB (@lem4623591 _55518 _55519 _55520) (@lem4623640 _55518 _55519 _55520)). Qed.
Lemma lem4623643 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4623644 (x : Prop) : (x = x) = True.
Proof. exact (@lem4623643 Prop x). Qed.
Lemma lem4623645 (_55518 : nat) (_55519 : nat) (_55520 : nat) : ((term324 _55518 _55519 _55520) = (term324 _55518 _55519 _55520)) = True.
Proof. exact (@lem4623644 (term324 _55518 _55519 _55520)). Qed.
Lemma lem4623646 (_55519 : nat) (_55518 : nat) (_55520 : nat) : ((term291 _55519 _55518 _55520) = (term327 _55519 _55518 _55520)) = True.
Proof. exact (TRANS (@lem4623641 _55518 _55519 _55520) (@lem4623645 _55518 _55519 _55520)). Qed.
Lemma lem4623647 (_55519 : nat) (_55518 : nat) (_55520 : nat) : True = ((term291 _55519 _55518 _55520) = (term327 _55519 _55518 _55520)).
Proof. exact (SYM (@lem4623646 _55519 _55518 _55520)). Qed.
Lemma lem4623648 (_55519 : nat) (_55518 : nat) (_55520 : nat) : (term291 _55519 _55518 _55520) = (term327 _55519 _55518 _55520).
Proof. exact (EQ_MP (@lem4623647 _55519 _55518 _55520) (@lem0)). Qed.
Lemma lem4623649 (_55519 : nat) (_55518 : nat) (_55520 : nat) (h1 : term136) : term327 _55519 _55518 _55520.
Proof. exact (EQ_MP (@lem4623648 _55519 _55518 _55520) (@lem4623398 _55519 _55518 _55520 h1)). Qed.
Lemma lem4623651 (b : Prop) (a : Prop) : (a \/ b) = (term310 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4623652 (_55518 : nat) (_55519 : nat) (_55520 : nat) : (term327 _55519 _55518 _55520) = (term328 _55518 _55519 _55520).
Proof. exact (@lem4623651 (term329 _55519 _55518 _55520) (term292 _55519 _55520)). Qed.
Lemma lem4623654 (a : Prop) (b : Prop) : (term330 a b) = (term331 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4623655 (_55519 : nat) (_55518 : nat) (_55520 : nat) : (term332 _55519 _55518 _55520) = (term333 _55519 _55518 _55520).
Proof. exact (@lem4623654 (term292 _55518 _55519) (Peano.le _55518 _55520)). Qed.
Lemma lem4623657 (a : Prop) : (term334 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4623658 (_55518 : nat) (_55519 : nat) : (term335 _55518 _55519) = (Peano.le _55518 _55519).
Proof. exact (@lem4623657 (Peano.le _55518 _55519)). Qed.
Lemma lem4623659 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4623660 (_55518 : nat) (_55519 : nat) : (term336 _55518 _55519) = (term337 _55518 _55519).
Proof. exact (MK_COMB (@lem4623659) (@lem4623658 _55518 _55519)). Qed.
Lemma lem4623661 (_55518 : nat) (_55520 : nat) : (term292 _55518 _55520) = (term292 _55518 _55520).
Proof. exact (eq_refl (term292 _55518 _55520)). Qed.
Lemma lem4623662 (_55519 : nat) (_55518 : nat) (_55520 : nat) : (term333 _55519 _55518 _55520) = (term338 _55519 _55518 _55520).
Proof. exact (MK_COMB (@lem4623660 _55518 _55519) (@lem4623661 _55518 _55520)). Qed.
Lemma lem4623663 (_55519 : nat) (_55518 : nat) (_55520 : nat) : (term332 _55519 _55518 _55520) = (term338 _55519 _55518 _55520).
Proof. exact (TRANS (@lem4623655 _55519 _55518 _55520) (@lem4623662 _55519 _55518 _55520)). Qed.
Lemma lem4623664 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4623665 (_55519 : nat) (_55518 : nat) (_55520 : nat) : (term339 _55519 _55518 _55520) = (term340 _55519 _55518 _55520).
Proof. exact (MK_COMB (@lem4623664) (@lem4623663 _55519 _55518 _55520)). Qed.
Lemma lem4623666 (_55519 : nat) (_55520 : nat) : (term292 _55519 _55520) = (term292 _55519 _55520).
Proof. exact (eq_refl (term292 _55519 _55520)). Qed.
Lemma lem4623667 (_55518 : nat) (_55519 : nat) (_55520 : nat) : (term328 _55518 _55519 _55520) = (term341 _55518 _55519 _55520).
Proof. exact (MK_COMB (@lem4623665 _55519 _55518 _55520) (@lem4623666 _55519 _55520)). Qed.
Lemma lem4623668 (_55518 : nat) (_55519 : nat) (_55520 : nat) : (term327 _55519 _55518 _55520) = (term341 _55518 _55519 _55520).
Proof. exact (TRANS (@lem4623652 _55518 _55519 _55520) (@lem4623667 _55518 _55519 _55520)). Qed.
Lemma lem4623670 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term120) (h2 : term294 x' a) (h3 : term261 a x s x') : term342 x' a.
Proof. exact (conj (@lem4623536 a x s x' h1 h3) (@lem4623544 x' a h2)). Qed.
Lemma lem4623672 (_55518 : nat) (_55519 : nat) (_55520 : nat) (h1 : term136) : term341 _55518 _55519 _55520.
Proof. exact (EQ_MP (@lem4623668 _55518 _55519 _55520) (@lem4623649 _55519 _55518 _55520 h1)). Qed.
Lemma lem4623673 (x' : nat -> nat) (a : nat) (h1 : term136) : term343 x' a.
Proof. exact (@lem4623672 (x' a) (term313 x' a) a h1). Qed.
Lemma lem4623676 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term120) (h3 : term294 x' a) (h4 : term261 a x s x') : term344 x' a.
Proof. exact (@lem4623673 x' a h1 (@lem4623670 a x s x' h2 h3 h4)). Qed.
Lemma lem4623677 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term120) (h3 : term294 x' a) (h4 : term261 a x s x') : term345 x' a.
Proof. exact (fun h0 : term346 x' a => @lem4623676 a x s x' h1 h2 h3 h4). Qed.
Lemma lem4623679 (p : Prop) : (term308 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4623680 (x' : nat -> nat) (a : nat) : (term345 x' a) = (term344 x' a).
Proof. exact (@lem4623679 (term346 x' a)). Qed.
Lemma lem4623681 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term120) (h3 : term294 x' a) (h4 : term261 a x s x') : term344 x' a.
Proof. exact (EQ_MP (@lem4623680 x' a) (@lem4623677 a x s x' h1 h2 h3 h4)). Qed.
Lemma lem4623683 (b : Prop) (a : Prop) : (a \/ b) = (term310 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4623686 (a : nat) (_55524 : nat) (s : nat -> Prop) : (term141 s _55524 a) = (term347 a _55524 s).
Proof. exact (@lem4623683 (Peano.le _55524 a) (term348 _55524 s)). Qed.
Lemma lem4623689 (_55524 : nat) (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term347 a _55524 s.
Proof. exact (EQ_MP (@lem4623686 a _55524 s) (@lem4623410 _55524 a x s x' h1)). Qed.
Lemma lem4623690 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term349 x' a s.
Proof. exact (@lem4623689 (term313 x' a) a x s x' h1). Qed.
Lemma lem4623693 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term120) (h3 : term294 x' a) (h4 : term261 a x s x') : term350 x' a s.
Proof. exact (@lem4623690 a x s x' h4 (@lem4623681 a x s x' h1 h2 h3 h4)). Qed.
Lemma lem4623694 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term120) (h3 : term294 x' a) (h4 : term261 a x s x') : term351 x' a s.
Proof. exact (fun h0 : term352 x' a s => @lem4623693 a x s x' h1 h2 h3 h4). Qed.
Lemma lem4623696 (p : Prop) : (term308 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4623697 (x' : nat -> nat) (a : nat) (s : nat -> Prop) : (term351 x' a s) = (term350 x' a s).
Proof. exact (@lem4623696 (term352 x' a s)). Qed.
Lemma lem4623698 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term120) (h3 : term294 x' a) (h4 : term261 a x s x') : term350 x' a s.
Proof. exact (EQ_MP (@lem4623697 x' a s) (@lem4623694 a x s x' h1 h2 h3 h4)). Qed.
Lemma lem4623700 (b : Prop) (a : Prop) : (a \/ b) = (term310 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4623703 (s : nat -> Prop) (x' : nat -> nat) (_55523 : nat) (x : nat) : (term293 x x' _55523 s) = (term353 s x' _55523 x).
Proof. exact (@lem4623700 (term354 x' _55523 s) ((x' _55523) = x)). Qed.
Lemma lem4623706 (_55523 : nat) (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term353 s x' _55523 x.
Proof. exact (EQ_MP (@lem4623703 s x' _55523 x) (@lem4623420 _55523 a x s x' h1)). Qed.
Lemma lem4623707 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term355 s x' a x.
Proof. exact (@lem4623706 (x' a) a x s x' h1). Qed.
Lemma lem4623710 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term120) (h3 : term294 x' a) (h4 : term261 a x s x') : (term313 x' a) = x.
Proof. exact (@lem4623707 a x s x' h4 (@lem4623698 a x s x' h1 h2 h3 h4)). Qed.
Lemma lem4623711 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term120) (h3 : term294 x' a) (h4 : term261 a x s x') : term356 x' a x.
Proof. exact (fun h0 : term357 x' a x => @lem4623710 a x s x' h1 h2 h3 h4). Qed.
Lemma lem4623713 (p : Prop) : (term317 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4623714 (x' : nat -> nat) (a : nat) (x : nat) : (term356 x' a x) = ((term313 x' a) = x).
Proof. exact (@lem4623713 ((term313 x' a) = x)). Qed.
Lemma lem4623715 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term120) (h3 : term294 x' a) (h4 : term261 a x s x') : (term313 x' a) = x.
Proof. exact (EQ_MP (@lem4623714 x' a x) (@lem4623711 a x s x' h1 h2 h3 h4)). Qed.
Lemma lem4623717 (_55523 : nat) (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term294 x' _55523.
Proof. exact (proj2 (@lem4623381 _55523 a x s x' h1)). Qed.
Lemma lem4623718 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term294 x' x.
Proof. exact (@lem4623717 x a x s x' h1). Qed.
Lemma lem4623719 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term318 x' x.
Proof. exact (fun h0 : term319 x' x => @lem4623718 a x s x' h1). Qed.
Lemma lem4623721 (p : Prop) : (term308 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4623722 (x' : nat -> nat) (x : nat) : (term318 x' x) = (term294 x' x).
Proof. exact (@lem4623721 (term319 x' x)). Qed.
Lemma lem4623723 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term294 x' x.
Proof. exact (EQ_MP (@lem4623722 x' x) (@lem4623719 a x s x' h1)). Qed.
Lemma lem4623726 (x' : nat -> nat) (a : nat) (h1 : term358 x' a) : term358 x' a.
Proof. exact (h1). Qed.
Lemma lem4623727 (x' : nat -> nat) (a : nat) (h1 : term358 x' a) : term359 x' a.
Proof. exact (fun h0 : term360 x' a => @lem4623726 x' a h1). Qed.
Lemma lem4623729 (p : Prop) : (term308 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4623730 (x' : nat -> nat) (a : nat) : (term359 x' a) = (term358 x' a).
Proof. exact (@lem4623729 (term360 x' a)). Qed.
Lemma lem4623731 (x' : nat -> nat) (a : nat) (h1 : term358 x' a) : term358 x' a.
Proof. exact (EQ_MP (@lem4623730 x' a) (@lem4623727 x' a h1)). Qed.
Lemma lem4623733 (_55522 : nat) (_55521 : nat) (h1 : term120) : term311 _55522 _55521.
Proof. exact (EQ_MP (@lem4623524 _55522 _55521) (@lem4623519 _55521 _55522 h1)). Qed.
Lemma lem4623734 (x' : nat -> nat) (a : nat) (h1 : term120) : term361 x' a.
Proof. exact (@lem4623733 (term313 x' a) (term313 x' a) h1). Qed.
Lemma lem4623737 (x' : nat -> nat) (a : nat) (h1 : term120) (h2 : term358 x' a) : term360 x' a.
Proof. exact (@lem4623734 x' a h1 (@lem4623731 x' a h2)). Qed.
Lemma lem4623738 (x' : nat -> nat) (a : nat) (h1 : term120) : term361 x' a.
Proof. exact (fun h0 : term358 x' a => @lem4623737 x' a h1 h0). Qed.
Lemma lem4623740 (p : Prop) : (term317 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4623741 (x' : nat -> nat) (a : nat) : (term361 x' a) = (term360 x' a).
Proof. exact (@lem4623740 (term360 x' a)). Qed.
Lemma lem4623742 (x' : nat -> nat) (a : nat) (h1 : term120) : term360 x' a.
Proof. exact (EQ_MP (@lem4623741 x' a) (@lem4623738 x' a h1)). Qed.
Lemma lem4623744 (b : Prop) (a : Prop) : (a \/ b) = (term310 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4623745 (_55534 : nat) (_55532 : nat) (_55531 : nat) (_55533 : nat) : (term302 _55533 _55534 _55531 _55532) = (term362 _55534 _55532 _55531 _55533).
Proof. exact (@lem4623744 (term300 _55533 _55534 _55531 _55532) (term363 _55531 _55533)). Qed.
Lemma lem4623747 (a : Prop) (b : Prop) : (term330 a b) = (term331 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4623748 (_55533 : nat) (_55534 : nat) (_55531 : nat) (_55532 : nat) : (term364 _55533 _55534 _55531 _55532) = (term365 _55533 _55534 _55531 _55532).
Proof. exact (@lem4623747 (term363 _55532 _55534) (term297 _55533 _55534 _55531 _55532)). Qed.
Lemma lem4623750 (a : Prop) : (term334 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4623751 (_55532 : nat) (_55534 : nat) : (term366 _55532 _55534) = (_55532 = _55534).
Proof. exact (@lem4623750 (_55532 = _55534)). Qed.
Lemma lem4623752 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4623753 (_55532 : nat) (_55534 : nat) : (term367 _55532 _55534) = (term368 _55532 _55534).
Proof. exact (MK_COMB (@lem4623752) (@lem4623751 _55532 _55534)). Qed.
Lemma lem4623755 (a : Prop) (b : Prop) : (term330 a b) = (term331 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4623756 (_55533 : nat) (_55534 : nat) (_55531 : nat) (_55532 : nat) : (term369 _55533 _55534 _55531 _55532) = (term370 _55533 _55534 _55531 _55532).
Proof. exact (@lem4623755 (Peano.le _55533 _55534) (term292 _55531 _55532)). Qed.
Lemma lem4623758 (a : Prop) : (term334 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4623759 (_55531 : nat) (_55532 : nat) : (term335 _55531 _55532) = (Peano.le _55531 _55532).
Proof. exact (@lem4623758 (Peano.le _55531 _55532)). Qed.
Lemma lem4623760 (_55533 : nat) (_55534 : nat) : (term371 _55533 _55534) = (term371 _55533 _55534).
Proof. exact (eq_refl (term371 _55533 _55534)). Qed.
Lemma lem4623761 (_55533 : nat) (_55534 : nat) (_55531 : nat) (_55532 : nat) : (term370 _55533 _55534 _55531 _55532) = (term372 _55533 _55534 _55531 _55532).
Proof. exact (MK_COMB (@lem4623760 _55533 _55534) (@lem4623759 _55531 _55532)). Qed.
Lemma lem4623762 (_55533 : nat) (_55534 : nat) (_55531 : nat) (_55532 : nat) : (term369 _55533 _55534 _55531 _55532) = (term372 _55533 _55534 _55531 _55532).
Proof. exact (TRANS (@lem4623756 _55533 _55534 _55531 _55532) (@lem4623761 _55533 _55534 _55531 _55532)). Qed.
Lemma lem4623763 (_55533 : nat) (_55534 : nat) (_55531 : nat) (_55532 : nat) : (term365 _55533 _55534 _55531 _55532) = (term373 _55533 _55534 _55531 _55532).
Proof. exact (MK_COMB (@lem4623753 _55532 _55534) (@lem4623762 _55533 _55534 _55531 _55532)). Qed.
Lemma lem4623764 (_55533 : nat) (_55534 : nat) (_55531 : nat) (_55532 : nat) : (term364 _55533 _55534 _55531 _55532) = (term373 _55533 _55534 _55531 _55532).
Proof. exact (TRANS (@lem4623748 _55533 _55534 _55531 _55532) (@lem4623763 _55533 _55534 _55531 _55532)). Qed.
Lemma lem4623765 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4623766 (_55533 : nat) (_55534 : nat) (_55531 : nat) (_55532 : nat) : (term374 _55533 _55534 _55531 _55532) = (term375 _55533 _55534 _55531 _55532).
Proof. exact (MK_COMB (@lem4623765) (@lem4623764 _55533 _55534 _55531 _55532)). Qed.
Lemma lem4623767 (_55531 : nat) (_55533 : nat) : (term363 _55531 _55533) = (term363 _55531 _55533).
Proof. exact (eq_refl (term363 _55531 _55533)). Qed.
Lemma lem4623768 (_55534 : nat) (_55532 : nat) (_55531 : nat) (_55533 : nat) : (term362 _55534 _55532 _55531 _55533) = (term376 _55534 _55532 _55531 _55533).
Proof. exact (MK_COMB (@lem4623766 _55533 _55534 _55531 _55532) (@lem4623767 _55531 _55533)). Qed.
Lemma lem4623769 (_55534 : nat) (_55532 : nat) (_55531 : nat) (_55533 : nat) : (term302 _55533 _55534 _55531 _55532) = (term376 _55534 _55532 _55531 _55533).
Proof. exact (TRANS (@lem4623745 _55534 _55532 _55531 _55533) (@lem4623768 _55534 _55532 _55531 _55533)). Qed.
Lemma lem4623771 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term120) (h2 : term261 a x s x') : term377 x x' a.
Proof. exact (conj (@lem4623723 a x s x' h2) (@lem4623742 x' a h1)). Qed.
Lemma lem4623772 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term120) (h3 : term294 x' a) (h4 : term261 a x s x') : term378 x x' a.
Proof. exact (conj (@lem4623715 a x s x' h1 h2 h3 h4) (@lem4623771 a x s x' h2 h4)). Qed.
Lemma lem4623774 (_55534 : nat) (_55532 : nat) (_55531 : nat) (_55533 : nat) : term376 _55534 _55532 _55531 _55533.
Proof. exact (EQ_MP (@lem4623769 _55534 _55532 _55531 _55533) (@lem4623472 _55533 _55534 _55531 _55532)). Qed.
Lemma lem4623775 (a : nat) (x' : nat -> nat) (x : nat) : term379 a x' x.
Proof. exact (@lem4623774 x (term313 x' a) (term313 x' a) (x' x)). Qed.
Lemma lem4623778 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term120) (h3 : term294 x' a) (h4 : term261 a x s x') : term380 a x' x.
Proof. exact (@lem4623775 a x' x (@lem4623772 a x s x' h1 h2 h3 h4)). Qed.
Lemma lem4623779 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term120) (h3 : term294 x' a) (h4 : term261 a x s x') : term381 a x' x.
Proof. exact (fun h0 : (term313 x' a) = (x' x) => @lem4623778 a x s x' h1 h2 h3 h4). Qed.
Lemma lem4623781 (p : Prop) : (term308 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4623782 (a : nat) (x' : nat -> nat) (x : nat) : (term381 a x' x) = (term380 a x' x).
Proof. exact (@lem4623781 ((term313 x' a) = (x' x))). Qed.
Lemma lem4623783 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term120) (h3 : term294 x' a) (h4 : term261 a x s x') : term380 a x' x.
Proof. exact (EQ_MP (@lem4623782 a x' x) (@lem4623779 a x s x' h1 h2 h3 h4)). Qed.
Lemma lem4623785 (b : Prop) (a : Prop) : (a \/ b) = (term310 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4623788 (x' : nat -> nat) (_55535 : nat) (_55536 : nat) : (term304 _55535 x' _55536) = (term382 x' _55535 _55536).
Proof. exact (@lem4623785 ((x' _55535) = (x' _55536)) (term363 _55535 _55536)). Qed.
Lemma lem4623791 (x' : nat -> nat) (_55535 : nat) (_55536 : nat) : term382 x' _55535 _55536.
Proof. exact (EQ_MP (@lem4623788 x' _55535 _55536) (@lem4623480 _55535 x' _55536)). Qed.
Lemma lem4623792 (x' : nat -> nat) (a : nat) (x : nat) : term383 x' a x.
Proof. exact (@lem4623791 x' (x' a) x). Qed.
Lemma lem4623795 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term120) (h3 : term294 x' a) (h4 : term261 a x s x') : term384 x' a x.
Proof. exact (@lem4623792 x' a x (@lem4623783 a x s x' h1 h2 h3 h4)). Qed.
Lemma lem4623796 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term120) (h3 : term294 x' a) (h4 : term261 a x s x') : term385 x' a x.
Proof. exact (fun h0 : (x' a) = x => @lem4623795 a x s x' h1 h2 h3 h4). Qed.
Lemma lem4623798 (p : Prop) : (term308 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4623799 (x' : nat -> nat) (a : nat) (x : nat) : (term385 x' a x) = (term384 x' a x).
Proof. exact (@lem4623798 ((x' a) = x)). Qed.
Lemma lem4623800 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term120) (h3 : term294 x' a) (h4 : term261 a x s x') : term384 x' a x.
Proof. exact (EQ_MP (@lem4623799 x' a x) (@lem4623796 a x s x' h1 h2 h3 h4)). Qed.
Lemma lem4623813 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4623814 (x : nat) (x' : nat -> nat) (_55523 : nat) (s : nat -> Prop) : (term386 s x' _55523 x) = (term293 x x' _55523 s).
Proof. exact (@lem4623813 ((x' _55523) = x) (term354 x' _55523 s)). Qed.
Lemma lem4623822 (x : nat) (x' : nat -> nat) (_55523 : nat) (s : nat -> Prop) : (term387 x x' _55523 s) = (term387 x x' _55523 s).
Proof. exact (eq_refl (term387 x x' _55523 s)). Qed.
Lemma lem4623823 (x : nat) (x' : nat -> nat) (_55523 : nat) (s : nat -> Prop) : ((term293 x x' _55523 s) = (term386 s x' _55523 x)) = ((term293 x x' _55523 s) = (term293 x x' _55523 s)).
Proof. exact (MK_COMB (@lem4623822 x x' _55523 s) (@lem4623814 x x' _55523 s)). Qed.
Lemma lem4623825 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4623826 (x : Prop) : (x = x) = True.
Proof. exact (@lem4623825 Prop x). Qed.
Lemma lem4623827 (x : nat) (x' : nat -> nat) (_55523 : nat) (s : nat -> Prop) : ((term293 x x' _55523 s) = (term293 x x' _55523 s)) = True.
Proof. exact (@lem4623826 (term293 x x' _55523 s)). Qed.
Lemma lem4623828 (s : nat -> Prop) (x' : nat -> nat) (_55523 : nat) (x : nat) : ((term293 x x' _55523 s) = (term386 s x' _55523 x)) = True.
Proof. exact (TRANS (@lem4623823 x x' _55523 s) (@lem4623827 x x' _55523 s)). Qed.
Lemma lem4623829 (s : nat -> Prop) (x' : nat -> nat) (_55523 : nat) (x : nat) : True = ((term293 x x' _55523 s) = (term386 s x' _55523 x)).
Proof. exact (SYM (@lem4623828 s x' _55523 x)). Qed.
Lemma lem4623830 (s : nat -> Prop) (x' : nat -> nat) (_55523 : nat) (x : nat) : (term293 x x' _55523 s) = (term386 s x' _55523 x).
Proof. exact (EQ_MP (@lem4623829 s x' _55523 x) (@lem0)). Qed.
Lemma lem4623831 (_55523 : nat) (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term386 s x' _55523 x.
Proof. exact (EQ_MP (@lem4623830 s x' _55523 x) (@lem4623420 _55523 a x s x' h1)). Qed.
Lemma lem4623833 (b : Prop) (a : Prop) : (a \/ b) = (term310 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4623836 (x : nat) (x' : nat -> nat) (_55523 : nat) (s : nat -> Prop) : (term386 s x' _55523 x) = (term388 x x' _55523 s).
Proof. exact (@lem4623833 ((x' _55523) = x) (term354 x' _55523 s)). Qed.
Lemma lem4623839 (_55523 : nat) (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term388 x x' _55523 s.
Proof. exact (EQ_MP (@lem4623836 x x' _55523 s) (@lem4623831 _55523 a x s x' h1)). Qed.
Lemma lem4623840 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term388 x x' a s.
Proof. exact (@lem4623839 a a x s x' h1). Qed.
Lemma lem4623843 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term120) (h3 : term294 x' a) (h4 : term261 a x s x') : term354 x' a s.
Proof. exact (@lem4623840 a x s x' h4 (@lem4623800 a x s x' h1 h2 h3 h4)). Qed.
Lemma lem4623844 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term120) (h3 : term294 x' a) (h4 : term261 a x s x') : term389 x' a s.
Proof. exact (fun h0 : term390 x' a s => @lem4623843 a x s x' h1 h2 h3 h4). Qed.
Lemma lem4623846 (p : Prop) : (term317 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4623847 (x' : nat -> nat) (a : nat) (s : nat -> Prop) : (term389 x' a s) = (term354 x' a s).
Proof. exact (@lem4623846 (term354 x' a s)). Qed.
Lemma lem4623848 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term120) (h3 : term294 x' a) (h4 : term261 a x s x') : term354 x' a s.
Proof. exact (EQ_MP (@lem4623847 x' a s) (@lem4623844 a x s x' h1 h2 h3 h4)). Qed.
Lemma lem4623854 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4623855 (a : nat) (_55524 : nat) (s : nat -> Prop) : (term141 s _55524 a) = (term391 a _55524 s).
Proof. exact (@lem4623854 (Peano.le _55524 a) (term348 _55524 s)). Qed.
Lemma lem4623861 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4623862 (a : nat) (_55524 : nat) (s : nat -> Prop) : (term392 s _55524 a) = (term393 a _55524 s).
Proof. exact (MK_COMB (@lem4623861) (@lem4623855 a _55524 s)). Qed.
Lemma lem4623868 (a : nat) (_55524 : nat) (s : nat -> Prop) : (term391 a _55524 s) = (term391 a _55524 s).
Proof. exact (eq_refl (term391 a _55524 s)). Qed.
Lemma lem4623869 (a : nat) (_55524 : nat) (s : nat -> Prop) : ((term141 s _55524 a) = (term391 a _55524 s)) = ((term391 a _55524 s) = (term391 a _55524 s)).
Proof. exact (MK_COMB (@lem4623862 a _55524 s) (@lem4623868 a _55524 s)). Qed.
Lemma lem4623871 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4623872 (x : Prop) : (x = x) = True.
Proof. exact (@lem4623871 Prop x). Qed.
Lemma lem4623873 (a : nat) (_55524 : nat) (s : nat -> Prop) : ((term391 a _55524 s) = (term391 a _55524 s)) = True.
Proof. exact (@lem4623872 (term391 a _55524 s)). Qed.
Lemma lem4623874 (a : nat) (_55524 : nat) (s : nat -> Prop) : ((term141 s _55524 a) = (term391 a _55524 s)) = True.
Proof. exact (TRANS (@lem4623869 a _55524 s) (@lem4623873 a _55524 s)). Qed.
Lemma lem4623875 (a : nat) (_55524 : nat) (s : nat -> Prop) : True = ((term141 s _55524 a) = (term391 a _55524 s)).
Proof. exact (SYM (@lem4623874 a _55524 s)). Qed.
Lemma lem4623876 (a : nat) (_55524 : nat) (s : nat -> Prop) : (term141 s _55524 a) = (term391 a _55524 s).
Proof. exact (EQ_MP (@lem4623875 a _55524 s) (@lem0)). Qed.
Lemma lem4623877 (_55524 : nat) (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term391 a _55524 s.
Proof. exact (EQ_MP (@lem4623876 a _55524 s) (@lem4623410 _55524 a x s x' h1)). Qed.
Lemma lem4623879 (b : Prop) (a : Prop) : (a \/ b) = (term310 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4623880 (s : nat -> Prop) (_55524 : nat) (a : nat) : (term391 a _55524 s) = (term394 s _55524 a).
Proof. exact (@lem4623879 (term348 _55524 s) (Peano.le _55524 a)). Qed.
Lemma lem4623882 (a : Prop) : (term334 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4623883 (_55524 : nat) (s : nat -> Prop) : (term395 _55524 s) = (@IN nat _55524 s).
Proof. exact (@lem4623882 (@IN nat _55524 s)). Qed.
Lemma lem4623884 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4623885 (_55524 : nat) (s : nat -> Prop) : (term396 _55524 s) = (term397 _55524 s).
Proof. exact (MK_COMB (@lem4623884) (@lem4623883 _55524 s)). Qed.
Lemma lem4623886 (_55524 : nat) (a : nat) : (Peano.le _55524 a) = (Peano.le _55524 a).
Proof. exact (eq_refl (Peano.le _55524 a)). Qed.
Lemma lem4623887 (s : nat -> Prop) (_55524 : nat) (a : nat) : (term394 s _55524 a) = (term137 s _55524 a).
Proof. exact (MK_COMB (@lem4623885 _55524 s) (@lem4623886 _55524 a)). Qed.
Lemma lem4623888 (s : nat -> Prop) (_55524 : nat) (a : nat) : (term391 a _55524 s) = (term137 s _55524 a).
Proof. exact (TRANS (@lem4623880 s _55524 a) (@lem4623887 s _55524 a)). Qed.
Lemma lem4623891 (_55524 : nat) (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term137 s _55524 a.
Proof. exact (EQ_MP (@lem4623888 s _55524 a) (@lem4623877 _55524 a x s x' h1)). Qed.
Lemma lem4623892 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term398 s x' a.
Proof. exact (@lem4623891 (x' a) a x s x' h1). Qed.
Lemma lem4623895 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term120) (h3 : term294 x' a) (h4 : term261 a x s x') : term319 x' a.
Proof. exact (@lem4623892 a x s x' h4 (@lem4623848 a x s x' h1 h2 h3 h4)). Qed.
Lemma lem4623896 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term120) (h3 : term261 a x s x') : term399 x' a.
Proof. exact (fun h0 : term294 x' a => @lem4623895 a x s x' h1 h2 h0 h3). Qed.
Lemma lem4623898 (p : Prop) : (term317 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4623899 (x' : nat -> nat) (a : nat) : (term399 x' a) = (term319 x' a).
Proof. exact (@lem4623898 (term319 x' a)). Qed.
Lemma lem4623900 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term120) (h3 : term261 a x s x') : term319 x' a.
Proof. exact (EQ_MP (@lem4623899 x' a) (@lem4623896 a x s x' h1 h2 h3)). Qed.
Lemma lem4623903 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4623905 (x' : nat -> nat) (_55523 : nat) : (term294 x' _55523) = (term400 x' _55523).
Proof. exact (@lem4623903 (term319 x' _55523)). Qed.
Lemma lem4623908 (_55523 : nat) (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term400 x' _55523.
Proof. exact (EQ_MP (@lem4623905 x' _55523) (@lem4623422 _55523 a x s x' h1)). Qed.
Lemma lem4623909 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term261 a x s x') : term400 x' a.
Proof. exact (@lem4623908 a a x s x' h1). Qed.
Lemma lem4623912 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term120) (h3 : term261 a x s x') : False.
Proof. exact (@lem4623909 a x s x' h3 (@lem4623900 a x s x' h1 h2 h3)). Qed.
Lemma lem4623913 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term120) (h3 : term261 a x s x') : term401.
Proof. exact (fun h0 : ~ False => @lem4623912 a x s x' h1 h2 h3). Qed.
Lemma lem4623915 (p : Prop) : (term317 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4623916 : term401 = False.
Proof. exact (@lem4623915 False). Qed.
Lemma lem4623917 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term120) (h3 : term261 a x s x') : False.
Proof. exact (EQ_MP (@lem4623916) (@lem4623913 a x s x' h1 h2 h3)). Qed.
Lemma lem4623918 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term120) (h3 : term261 a x s x') : term120 = False.
Proof. exact (prop_ext (fun h4 : term120 => @lem4623917 a x s x' h1 h2 h3) (fun h4 : False => @lem4623325 h2)). Qed.
Lemma lem4623919 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term120) (h3 : term261 a x s x') : False.
Proof. exact (EQ_MP (@lem4623918 a x s x' h1 h2 h3) (@lem4623325 h2)). Qed.
Lemma lem4623920 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term120) (h3 : term261 a x s x') : (term261 a x s x') = False.
Proof. exact (prop_ext (fun h4 : term261 a x s x' => @lem4623919 a x s x' h1 h2 h3) (fun h4 : False => @lem4623278 a x s x' h3)). Qed.
Lemma lem4623921 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term120) (h3 : term261 a x s x') : False.
Proof. exact (EQ_MP (@lem4623920 a x s x' h1 h2 h3) (@lem4623278 a x s x' h3)). Qed.
Lemma lem4623922 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term120) (h3 : term261 a x s x') : term120 = False.
Proof. exact (prop_ext (fun h4 : term120 => @lem4623921 a x s x' h1 h2 h3) (fun h4 : False => @lem4623208 h2)). Qed.
Lemma lem4623923 (a : nat) (x : nat) (s : nat -> Prop) (x' : nat -> nat) (h1 : term136) (h2 : term120) (h3 : term261 a x s x') : False.
Proof. exact (EQ_MP (@lem4623922 a x s x' h1 h2 h3) (@lem4623208 h2)). Qed.
Lemma lem4623924 (a : nat) (x : nat) (s : nat -> Prop) (h1 : term136) (h2 : term120) (h3 : term264 a x s) : False.
Proof. exact (ex_elim (@lem4623152 a x s h3) (fun x' : nat -> nat => fun h0 : term263 a x s x' => @lem4623923 a x s x' h1 h2 h0)). Qed.
Lemma lem4623925 (x : nat) (s : nat -> Prop) (h1 : term136) (h2 : term120) (h3 : term266 x s) : False.
Proof. exact (ex_elim (@lem4623151 x s h3) (fun a : nat => fun h0 : term265 x s a => @lem4623924 a x s h1 h2 h0)). Qed.
Lemma lem4623926 (x : nat) (h1 : term136) (h2 : term120) (h3 : term268 x) : False.
Proof. exact (ex_elim (@lem4623150 x h3) (fun s : nat -> Prop => fun h0 : term267 x s => @lem4623925 x s h1 h2 h0)). Qed.
Lemma lem4623927 (h1 : term136) (h2 : term120) (h3 : term113) : False.
Proof. exact (ex_elim (@lem4622998 h3) (fun x : nat => fun h0 : term269 x => @lem4623926 x h1 h2 h0)). Qed.
Lemma lem4623928 (h1 : term136) (h2 : term120) (h3 : term113) : term120 = False.
Proof. exact (prop_ext (fun h4 : term120 => @lem4623927 h1 h2 h3) (fun h4 : False => @lem4623149 h2)). Qed.
Lemma lem4623929 (h1 : term136) (h2 : term120) (h3 : term113) : False.
Proof. exact (EQ_MP (@lem4623928 h1 h2 h3) (@lem4623149 h2)). Qed.
Lemma lem4623930 (h1 : term136) (h2 : term113) : term118.
Proof. exact (fun h0 : term120 => @lem4623929 h1 h0 h2). Qed.
Lemma lem4623931 : term118 = term119.
Proof. exact (@lem69 term120). Qed.
Lemma lem4623932 (h1 : term136) (h2 : term113) : term119.
Proof. exact (EQ_MP (@lem4623931) (@lem4623930 h1 h2)). Qed.
Lemma lem4623933 (h1 : term113) : term123.
Proof. exact (fun h0 : term136 => @lem4623932 h0 h1). Qed.
Lemma lem4623934 : term125.
Proof. exact (fun h0 : term113 => @lem4623933 h0). Qed.
Lemma lem4623935 : term114.
Proof. exact (EQ_MP (@lem4622646) (@lem4623934)). Qed.
Lemma lem4623937 : term114.
Proof. exact (@lem4622345 (@lem4623935)). Qed.
Lemma lem4623938 (h1 : term113) : term122.
Proof. exact (@lem4623937 (@lem4622330 h1)). Qed.
Lemma lem4623939 (h1 : term113) : term118.
Proof. exact (@lem4623938 h1 (@lem93743)). Qed.
Lemma lem4623940 (h1 : term113) : False.
Proof. exact (@lem4623939 h1 (@lem96155)). Qed.
Lemma lem4623941 (h1 : term113) : term113 = False.
Proof. exact (prop_ext (fun h2 : term113 => @lem4623940 h1) (fun h2 : False => @lem4622330 h1)). Qed.
Lemma lem4623942 (h1 : term113) : False.
Proof. exact (EQ_MP (@lem4623941 h1) (@lem4622330 h1)). Qed.
Lemma lem4623943 : term112.
Proof. exact (fun h0 : term113 => @lem4623942 h0). Qed.
Lemma lem4623944 : term109.
Proof. exact (EQ_MP (@lem4622329) (@lem4623943)). Qed.
Lemma lem4623945 : term68.
Proof. exact (EQ_MP (@lem4622325) (@lem4623944)). Qed.
Lemma lem4623946 : term77.
Proof. exact (@lem4622160 (@lem4623945)). Qed.
Lemma lem4623947 (s : nat -> Prop) : term402 s.
Proof. exact (@lem4623946 s). Qed.
Lemma lem4623948 (s : nat -> Prop) : (term402 s) = (term73 s).
Proof. exact (eq_refl (term402 s)). Qed.
Lemma lem4623949 (s : nat -> Prop) : term73 s.
Proof. exact (EQ_MP (@lem4623948 s) (@lem4623947 s)). Qed.
Lemma lem4623950 (s : nat -> Prop) (h1 : term47 s) : term47 s.
Proof. exact (h1). Qed.
Lemma lem4623951 (s : nat -> Prop) (n : nat) (h1 : term139 s n) : term139 s n.
Proof. exact (h1). Qed.
Lemma lem4623953 {A : Type'} (s : A -> Prop) : term11 A s.
Proof. exact (EQ_MP (@lem4622086 A s) (@lem4622085 A s)). Qed.
Lemma lem4623954 (s : nat -> Prop) : term403 s.
Proof. exact (@lem4623953 nat s). Qed.
Lemma lem4623958 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem4622065 n) (@lem4622064 n)). Qed.
Lemma lem4623959 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4623960 (n : nat) : (term404 n) = (and True).
Proof. exact (MK_COMB (@lem4623959) (@lem4623958 n)). Qed.
Lemma lem4623965 (s : nat -> Prop) (n : nat) : (term405 s n) = (term405 s n).
Proof. exact (eq_refl (term405 s n)). Qed.
Lemma lem4623966 (s : nat -> Prop) (n : nat) : (term406 s n) = (term407 s n).
Proof. exact (MK_COMB (@lem4623960 n) (@lem4623965 s n)). Qed.
Lemma lem4623968 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4623969 (s : nat -> Prop) (n : nat) : (term407 s n) = (term405 s n).
Proof. exact (@lem4623968 (term405 s n)). Qed.
Lemma lem4623974 (s : nat -> Prop) (n : nat) : (term406 s n) = (term405 s n).
Proof. exact (TRANS (@lem4623966 s n) (@lem4623969 s n)). Qed.
Lemma lem4623975 (s : nat -> Prop) (n : nat) : (term405 s n) = (term406 s n).
Proof. exact (SYM (@lem4623974 s n)). Qed.
Lemma lem4624000 {_83095 : Type'} : term408 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4624001 {_83095 : Type'} (p : _83095 -> Prop) : term409 _83095 p.
Proof. exact (@lem4624000 _83095 p). Qed.
Lemma lem4624002 {_83095 : Type'} (p : _83095 -> Prop) : (term409 _83095 p) = (term410 _83095 p).
Proof. exact (eq_refl (term409 _83095 p)). Qed.
Lemma lem4624003 {_83095 : Type'} (p : _83095 -> Prop) : term410 _83095 p.
Proof. exact (EQ_MP (@lem4624002 _83095 p) (@lem4624001 _83095 p)). Qed.
Lemma lem4624004 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term411 _83095 p x.
Proof. exact (@lem4624003 _83095 p x). Qed.
Lemma lem4624005 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term411 _83095 p x) = ((term412 _83095 x p) = (p x)).
Proof. exact (eq_refl (term411 _83095 p x)). Qed.
Lemma lem4624014 {A : Type'} (s : A -> Prop) : term413 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem4624015 {A : Type'} (s : A -> Prop) : (term413 A s) = (term414 A s).
Proof. exact (eq_refl (term413 A s)). Qed.
Lemma lem4624016 {A : Type'} (s : A -> Prop) : term414 A s.
Proof. exact (EQ_MP (@lem4624015 A s) (@lem4624014 A s)). Qed.
Lemma lem4624017 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term415 A s t.
Proof. exact (@lem4624016 A s t). Qed.
Lemma lem4624018 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term415 A s t) = ((@SUBSET A s t) = (term416 A s t)).
Proof. exact (eq_refl (term415 A s t)). Qed.
Lemma lem4624020 (x : nat) (s : nat -> Prop) (n : nat) (h1 : term139 s n) : term417 s n x.
Proof. exact (@lem4623951 s n h1 x). Qed.
Lemma lem4624021 (s : nat -> Prop) (x : nat) (n : nat) : (term417 s n x) = (term137 s x n).
Proof. exact (eq_refl (term417 s n x)). Qed.
Lemma lem4624022 (x : nat) (s : nat -> Prop) (n : nat) (h1 : term139 s n) : term137 s x n.
Proof. exact (EQ_MP (@lem4624021 s x n) (@lem4624020 x s n h1)). Qed.
Lemma lem4624023 (x : nat) (s : nat -> Prop) (h1 : @IN nat x s) : @IN nat x s.
Proof. exact (h1). Qed.
Lemma lem4624024 (n : nat) (x : nat) (s : nat -> Prop) (h1 : term139 s n) (h2 : @IN nat x s) : Peano.le x n.
Proof. exact (@lem4624022 x s n h1 (@lem4624023 x s h2)). Qed.
Lemma lem4624025 (x : nat) (n : nat) : (Peano.le x n) = ((Peano.le x n) = True).
Proof. exact (@lem7 (Peano.le x n)). Qed.
Lemma lem4624026 (n : nat) (x : nat) (s : nat -> Prop) (h1 : term139 s n) (h2 : @IN nat x s) : (Peano.le x n) = True.
Proof. exact (EQ_MP (@lem4624025 x n) (@lem4624024 n x s h1 h2)). Qed.
Lemma lem4624033 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term416 A s t).
Proof. exact (EQ_MP (@lem4624018 A s t) (@lem4624017 A s t)). Qed.
Lemma lem4624034 (s : nat -> Prop) (t : nat -> Prop) : (@SUBSET nat s t) = (term418 s t).
Proof. exact (@lem4624033 nat s t). Qed.
Lemma lem4624035 (s : nat -> Prop) (n : nat) : (term405 s n) = (term419 s n).
Proof. exact (@lem4624034 s (term420 n)). Qed.
Lemma lem4624043 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term421 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4624044 (p : Prop) (q : Prop) (p' : Prop) : term422 p q p'.
Proof. exact (fun q' : Prop => @lem4624043 p q p' q'). Qed.
Lemma lem4624045 (p : Prop) (q : Prop) : term423 p q.
Proof. exact (fun p' : Prop => @lem4624044 p q p'). Qed.
Lemma lem4624046 (s : nat -> Prop) (x : nat) (n : nat) : term424 s x n.
Proof. exact (@lem4624045 (@IN nat x s) (term425 x n)). Qed.
Lemma lem4624047 (s : nat -> Prop) (x : nat) (n : nat) (p' : Prop) : term426 s x n p'.
Proof. exact (@lem4624046 s x n p'). Qed.
Lemma lem4624048 (s : nat -> Prop) (x : nat) (n : nat) (p' : Prop) : (term426 s x n p') = (term427 s x n p').
Proof. exact (eq_refl (term426 s x n p')). Qed.
Lemma lem4624049 (s : nat -> Prop) (x : nat) (n : nat) (p' : Prop) : term427 s x n p'.
Proof. exact (EQ_MP (@lem4624048 s x n p') (@lem4624047 s x n p')). Qed.
Lemma lem4624050 (s : nat -> Prop) (x : nat) (n : nat) (p' : Prop) (q' : Prop) : term428 s x n p' q'.
Proof. exact (@lem4624049 s x n p' q'). Qed.
Lemma lem4624051 (s : nat -> Prop) (x : nat) (n : nat) (p' : Prop) (q' : Prop) : (term428 s x n p' q') = (term429 s x n p' q').
Proof. exact (eq_refl (term428 s x n p' q')). Qed.
Lemma lem4624052 (s : nat -> Prop) (x : nat) (n : nat) (p' : Prop) (q' : Prop) : term429 s x n p' q'.
Proof. exact (EQ_MP (@lem4624051 s x n p' q') (@lem4624050 s x n p' q')). Qed.
Lemma lem4624053 (x : nat) (s : nat -> Prop) : (@IN nat x s) = (@IN nat x s).
Proof. exact (eq_refl (@IN nat x s)). Qed.
Lemma lem4624054 (n : nat) (x : nat) (s : nat -> Prop) (q' : Prop) : term430 n x s q'.
Proof. exact (@lem4624052 s x n (@IN nat x s) q'). Qed.
Lemma lem4624055 (n : nat) (x : nat) (s : nat -> Prop) (q' : Prop) : term431 n x s q'.
Proof. exact (@lem4624054 n x s q' (@lem4624053 x s)). Qed.
Lemma lem4624056 (x : nat) (s : nat -> Prop) (h1 : @IN nat x s) : @IN nat x s.
Proof. exact (h1). Qed.
Lemma lem4624057 (x : nat) (s : nat -> Prop) : (@IN nat x s) = ((@IN nat x s) = True).
Proof. exact (@lem7 (@IN nat x s)). Qed.
Lemma lem4624060 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term412 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4624005 _83095 p x) (@lem4624004 _83095 p x)). Qed.
Lemma lem4624061 (p : nat -> Prop) (x : nat) : (term432 x p) = (p x).
Proof. exact (@lem4624060 nat p x). Qed.
Lemma lem4624062 (n : nat) (x : nat) : (term433 x n) = (term434 n x).
Proof. exact (@lem4624061 (term435 n) x). Qed.
Lemma lem4624063 (m : nat) (n : nat) : (term434 n m) = (Peano.le m n).
Proof. exact (eq_refl (term434 n m)). Qed.
Lemma lem4624064 (GEN_PVAR_191 : nat) : (@SETSPEC nat GEN_PVAR_191) = (@SETSPEC nat GEN_PVAR_191).
Proof. exact (eq_refl (@SETSPEC nat GEN_PVAR_191)). Qed.
Lemma lem4624065 (GEN_PVAR_191 : nat) (m : nat) (n : nat) : (term436 GEN_PVAR_191 n m) = (term437 GEN_PVAR_191 m n).
Proof. exact (MK_COMB (@lem4624064 GEN_PVAR_191) (@lem4624063 m n)). Qed.
Lemma lem4624066 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem4624067 (GEN_PVAR_191 : nat) (n : nat) (m : nat) : (term438 GEN_PVAR_191 n m) = (term439 GEN_PVAR_191 n m).
Proof. exact (MK_COMB (@lem4624065 GEN_PVAR_191 m n) (@lem4624066 m)). Qed.
Lemma lem4624068 (GEN_PVAR_191 : nat) (n : nat) : (term440 GEN_PVAR_191 n) = (term441 GEN_PVAR_191 n).
Proof. exact (fun_ext (fun m : nat => @lem4624067 GEN_PVAR_191 n m)). Qed.
Lemma lem4624069 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4624070 (GEN_PVAR_191 : nat) (n : nat) : (term442 GEN_PVAR_191 n) = (term443 GEN_PVAR_191 n).
Proof. exact (MK_COMB (@lem4624069) (@lem4624068 GEN_PVAR_191 n)). Qed.
Lemma lem4624071 (n : nat) : (term444 n) = (term445 n).
Proof. exact (fun_ext (fun GEN_PVAR_191 : nat => @lem4624070 GEN_PVAR_191 n)). Qed.
Lemma lem4624072 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem4624073 (n : nat) : (term446 n) = (term420 n).
Proof. exact (MK_COMB (@lem4624072) (@lem4624071 n)). Qed.
Lemma lem4624074 (x : nat) : (@IN nat x) = (@IN nat x).
Proof. exact (eq_refl (@IN nat x)). Qed.
Lemma lem4624075 (x : nat) (n : nat) : (term433 x n) = (term425 x n).
Proof. exact (MK_COMB (@lem4624074 x) (@lem4624073 n)). Qed.
Lemma lem4624076 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4624077 (x : nat) (n : nat) : (term447 x n) = (term448 x n).
Proof. exact (MK_COMB (@lem4624076) (@lem4624075 x n)). Qed.
Lemma lem4624078 (x : nat) (n : nat) : (term434 n x) = (Peano.le x n).
Proof. exact (eq_refl (term434 n x)). Qed.
Lemma lem4624079 (x : nat) (n : nat) : ((term433 x n) = (term434 n x)) = ((term425 x n) = (Peano.le x n)).
Proof. exact (MK_COMB (@lem4624077 x n) (@lem4624078 x n)). Qed.
Lemma lem4624080 (x : nat) (n : nat) : (term425 x n) = (Peano.le x n).
Proof. exact (EQ_MP (@lem4624079 x n) (@lem4624062 n x)). Qed.
Lemma lem4624082 (x : nat) (s : nat -> Prop) (n : nat) (h1 : term139 s n) : term449 s x n.
Proof. exact (fun h0 : @IN nat x s => @lem4624026 n x s h1 h0). Qed.
Lemma lem4624084 (x : nat) (s : nat -> Prop) (h1 : @IN nat x s) : (@IN nat x s) = True.
Proof. exact (EQ_MP (@lem4624057 x s) (@lem4624056 x s h1)). Qed.
Lemma lem4624085 (x : nat) (s : nat -> Prop) (h1 : @IN nat x s) : True = (@IN nat x s).
Proof. exact (SYM (@lem4624084 x s h1)). Qed.
Lemma lem4624086 (x : nat) (s : nat -> Prop) (h1 : @IN nat x s) : @IN nat x s.
Proof. exact (EQ_MP (@lem4624085 x s h1) (@lem0)). Qed.
Lemma lem4624087 (n : nat) (x : nat) (s : nat -> Prop) (h1 : term139 s n) (h2 : @IN nat x s) : (Peano.le x n) = True.
Proof. exact (@lem4624082 x s n h1 (@lem4624086 x s h2)). Qed.
Lemma lem4624088 (n : nat) (x : nat) (s : nat -> Prop) (h1 : term139 s n) (h2 : @IN nat x s) : (term425 x n) = True.
Proof. exact (TRANS (@lem4624080 x n) (@lem4624087 n x s h1 h2)). Qed.
Lemma lem4624089 (x : nat) (s : nat -> Prop) (n : nat) (h1 : term139 s n) : term450 s x n.
Proof. exact (fun h0 : @IN nat x s => @lem4624088 n x s h1 h0). Qed.
Lemma lem4624090 (n : nat) (x : nat) (s : nat -> Prop) : term451 n x s.
Proof. exact (@lem4624055 n x s True). Qed.
Lemma lem4624091 (x : nat) (s : nat -> Prop) (n : nat) (h1 : term139 s n) : (term452 s x n) = (term453 x s).
Proof. exact (@lem4624090 n x s (@lem4624089 x s n h1)). Qed.
Lemma lem4624093 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4624094 (x : nat) (s : nat -> Prop) : (term453 x s) = True.
Proof. exact (@lem4624093 (@IN nat x s)). Qed.
Lemma lem4624095 (x : nat) (s : nat -> Prop) (n : nat) (h1 : term139 s n) : (term452 s x n) = True.
Proof. exact (TRANS (@lem4624091 x s n h1) (@lem4624094 x s)). Qed.
Lemma lem4624096 (s : nat -> Prop) (n : nat) (h1 : term139 s n) : (term454 s n) = term83.
Proof. exact (fun_ext (fun x : nat => @lem4624095 x s n h1)). Qed.
Lemma lem4624097 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4624098 (s : nat -> Prop) (n : nat) (h1 : term139 s n) : (term419 s n) = term85.
Proof. exact (MK_COMB (@lem4624097) (@lem4624096 s n h1)). Qed.
Lemma lem4624100 {A : Type'} (t : Prop) : (term86 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4624101 (t : Prop) : (term87 t) = t.
Proof. exact (@lem4624100 nat t). Qed.
Lemma lem4624102 : term85 = True.
Proof. exact (@lem4624101 True). Qed.
Lemma lem4624103 (s : nat -> Prop) (n : nat) (h1 : term139 s n) : (term419 s n) = True.
Proof. exact (TRANS (@lem4624098 s n h1) (@lem4624102)). Qed.
Lemma lem4624104 (s : nat -> Prop) (n : nat) (h1 : term139 s n) : (term405 s n) = True.
Proof. exact (TRANS (@lem4624035 s n) (@lem4624103 s n h1)). Qed.
Lemma lem4624105 (s : nat -> Prop) (n : nat) (h1 : term139 s n) : True = (term405 s n).
Proof. exact (SYM (@lem4624104 s n h1)). Qed.
Lemma lem4624106 (s : nat -> Prop) (n : nat) (h1 : term139 s n) : term405 s n.
Proof. exact (EQ_MP (@lem4624105 s n h1) (@lem0)). Qed.
Lemma lem4624107 (s : nat -> Prop) (n : nat) (h1 : term139 s n) : term406 s n.
Proof. exact (EQ_MP (@lem4623975 s n) (@lem4624106 s n h1)). Qed.
Lemma lem4624108 (s : nat -> Prop) (n : nat) (h1 : term139 s n) : term455 s.
Proof. exact (ex_intro (term456 s) (term420 n) (@lem4624107 s n h1)). Qed.
Lemma lem4624109 (s : nat -> Prop) (n : nat) (h1 : term139 s n) : @FINITE nat s.
Proof. exact (@lem4623954 s (@lem4624108 s n h1)). Qed.
Lemma lem4624110 (s : nat -> Prop) (h1 : term47 s) : @FINITE nat s.
Proof. exact (ex_elim (@lem4623950 s h1) (fun n : nat => fun h0 : term140 s n => @lem4624109 s n h0)). Qed.
Lemma lem4624111 (s : nat -> Prop) : term457 s.
Proof. exact (fun h0 : term47 s => @lem4624110 s h0). Qed.
Lemma lem4624112 (s : nat -> Prop) : term458 s.
Proof. exact (conj (@lem4623949 s) (@lem4624111 s)). Qed.
Lemma lem4624113 (s : nat -> Prop) : (term458 s) = ((@FINITE nat s) = (term47 s)).
Proof. exact (@lem32 (@FINITE nat s) (term47 s)). Qed.
Lemma lem4624114 (s : nat -> Prop) : (@FINITE nat s) = (term47 s).
Proof. exact (EQ_MP (@lem4624113 s) (@lem4624112 s)). Qed.
Lemma lem4624119 : term459.
Proof. exact (fun s : nat -> Prop => @lem4624114 s). Qed.
