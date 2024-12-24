Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LENGTH_REPLICATE_term_abbrevs.
Require Import thm0_spec.
Require Import thm1097080_spec.
Require Import thm1099511_spec.
Require Import thm1099512_spec.
Require Import thm1099517_spec.
Require Import thm1099518_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem1138072 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1138073 {_26795 : Type'} : term1 _26795.
Proof. exact (@lem1138072 (term2 _26795)). Qed.
Lemma lem1138074 {_26795 : Type'} : (term3 _26795) = (term4 _26795).
Proof. exact (eq_refl (term3 _26795)). Qed.
Lemma lem1138075 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1138076 {_26795 : Type'} : (term5 _26795) = (term6 _26795).
Proof. exact (MK_COMB (@lem1138075) (@lem1138074 _26795)). Qed.
Lemma lem1138077 {_26795 : Type'} (n : nat) : (term7 _26795 n) = (term8 _26795 n).
Proof. exact (eq_refl (term7 _26795 n)). Qed.
Lemma lem1138078 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1138079 {_26795 : Type'} (n : nat) : (term9 _26795 n) = (term10 _26795 n).
Proof. exact (MK_COMB (@lem1138078) (@lem1138077 _26795 n)). Qed.
Lemma lem1138080 {_26795 : Type'} (n : nat) : (term11 _26795 n) = (term12 _26795 n).
Proof. exact (eq_refl (term11 _26795 n)). Qed.
Lemma lem1138081 {_26795 : Type'} (n : nat) : (term13 _26795 n) = (term14 _26795 n).
Proof. exact (MK_COMB (@lem1138079 _26795 n) (@lem1138080 _26795 n)). Qed.
Lemma lem1138082 {_26795 : Type'} : (term15 _26795) = (term16 _26795).
Proof. exact (fun_ext (fun n : nat => @lem1138081 _26795 n)). Qed.
Lemma lem1138083 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1138084 {_26795 : Type'} : (term17 _26795) = (term18 _26795).
Proof. exact (MK_COMB (@lem1138083) (@lem1138082 _26795)). Qed.
Lemma lem1138085 {_26795 : Type'} : (term19 _26795) = (term20 _26795).
Proof. exact (MK_COMB (@lem1138076 _26795) (@lem1138084 _26795)). Qed.
Lemma lem1138086 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1138087 {_26795 : Type'} : (term21 _26795) = (term22 _26795).
Proof. exact (MK_COMB (@lem1138086) (@lem1138085 _26795)). Qed.
Lemma lem1138088 {_26795 : Type'} (n : nat) : (term7 _26795 n) = (term8 _26795 n).
Proof. exact (eq_refl (term7 _26795 n)). Qed.
Lemma lem1138089 {_26795 : Type'} : (term23 _26795) = (term2 _26795).
Proof. exact (fun_ext (fun n : nat => @lem1138088 _26795 n)). Qed.
Lemma lem1138090 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1138091 {_26795 : Type'} : (term24 _26795) = (term25 _26795).
Proof. exact (MK_COMB (@lem1138090) (@lem1138089 _26795)). Qed.
Lemma lem1138092 {_26795 : Type'} : (term1 _26795) = (term26 _26795).
Proof. exact (MK_COMB (@lem1138087 _26795) (@lem1138091 _26795)). Qed.
Lemma lem1138093 {_26795 : Type'} : term26 _26795.
Proof. exact (EQ_MP (@lem1138092 _26795) (@lem1138073 _26795)). Qed.
Lemma lem1138094 {_26795 : Type'} (n : nat) (h1 : term8 _26795 n) : term8 _26795 n.
Proof. exact (h1). Qed.
Lemma lem1138112 {_25272 : Type'} (x : _25272) : (term27 _25272 x) = (@nil _25272).
Proof. exact (EQ_MP (@lem1099512 _25272 x) (@lem1099511 _25272 x)). Qed.
Lemma lem1138113 {_26795 : Type'} (x : _26795) : (term27 _26795 x) = (@nil _26795).
Proof. exact (@lem1138112 _26795 x). Qed.
Lemma lem1138114 {_26795 : Type'} : (@List.length _26795) = (@List.length _26795).
Proof. exact (eq_refl (@List.length _26795)). Qed.
Lemma lem1138115 {_26795 : Type'} (x : _26795) : (term28 _26795 x) = (@List.length _26795 (@nil _26795)).
Proof. exact (MK_COMB (@lem1138114 _26795) (@lem1138113 _26795 x)). Qed.
Lemma lem1138117 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1138118 {_26795 : Type'} : (@List.length _26795 (@nil _26795)) = (NUMERAL 0).
Proof. exact (@lem1138117 _26795). Qed.
Lemma lem1138119 {_26795 : Type'} (x : _26795) : (term28 _26795 x) = (NUMERAL 0).
Proof. exact (TRANS (@lem1138115 _26795 x) (@lem1138118 _26795)). Qed.
Lemma lem1138120 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1138121 {_26795 : Type'} (x : _26795) : (term29 _26795 x) = term30.
Proof. exact (MK_COMB (@lem1138120) (@lem1138119 _26795 x)). Qed.
Lemma lem1138122 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1138123 {_26795 : Type'} (x : _26795) : ((term28 _26795 x) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1138121 _26795 x) (@lem1138122)). Qed.
Lemma lem1138125 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1138126 (x : nat) : (x = x) = True.
Proof. exact (@lem1138125 nat x). Qed.
Lemma lem1138127 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1138126 (NUMERAL 0)). Qed.
Lemma lem1138128 {_26795 : Type'} (x : _26795) : ((term28 _26795 x) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem1138123 _26795 x) (@lem1138127)). Qed.
Lemma lem1138129 {_26795 : Type'} : (term31 _26795) = (term32 _26795).
Proof. exact (fun_ext (fun x : _26795 => @lem1138128 _26795 x)). Qed.
Lemma lem1138130 {_26795 : Type'} : (@all _26795) = (@all _26795).
Proof. exact (eq_refl (@all _26795)). Qed.
Lemma lem1138131 {_26795 : Type'} : (term4 _26795) = (term33 _26795).
Proof. exact (MK_COMB (@lem1138130 _26795) (@lem1138129 _26795)). Qed.
Lemma lem1138133 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1138134 {_26795 : Type'} (t : Prop) : (term34 _26795 t) = t.
Proof. exact (@lem1138133 _26795 t). Qed.
Lemma lem1138135 {_26795 : Type'} : (term33 _26795) = True.
Proof. exact (@lem1138134 _26795 True). Qed.
Lemma lem1138136 {_26795 : Type'} : (term4 _26795) = True.
Proof. exact (TRANS (@lem1138131 _26795) (@lem1138135 _26795)). Qed.
Lemma lem1138137 {_26795 : Type'} : True = (term4 _26795).
Proof. exact (SYM (@lem1138136 _26795)). Qed.
Lemma lem1138138 {_26795 : Type'} : term4 _26795.
Proof. exact (EQ_MP (@lem1138137 _26795) (@lem0)). Qed.
Lemma lem1138141 {A : Type'} : term35 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem1138142 {A : Type'} (h : A) : term36 A h.
Proof. exact (@lem1138141 A h). Qed.
Lemma lem1138143 {A : Type'} (h : A) : (term36 A h) = (term37 A h).
Proof. exact (eq_refl (term36 A h)). Qed.
Lemma lem1138144 {A : Type'} (h : A) : term37 A h.
Proof. exact (EQ_MP (@lem1138143 A h) (@lem1138142 A h)). Qed.
Lemma lem1138145 {A : Type'} (h : A) (t : list A) : term38 A h t.
Proof. exact (@lem1138144 A h t). Qed.
Lemma lem1138146 {A : Type'} (h : A) (t : list A) : (term38 A h t) = ((term39 A h t) = (term40 A t)).
Proof. exact (eq_refl (term38 A h t)). Qed.
Lemma lem1138149 {_26795 : Type'} (x : _26795) (n : nat) (h1 : term8 _26795 n) : term41 _26795 n x.
Proof. exact (@lem1138094 _26795 n h1 x). Qed.
Lemma lem1138150 {_26795 : Type'} (x : _26795) (n : nat) : (term41 _26795 n x) = ((term42 _26795 n x) = n).
Proof. exact (eq_refl (term41 _26795 n x)). Qed.
Lemma lem1138159 {_25272 : Type'} (n : nat) (x : _25272) : (term43 _25272 n x) = (term44 _25272 n x).
Proof. exact (EQ_MP (@lem1099518 _25272 n x) (@lem1099517 _25272 n x)). Qed.
Lemma lem1138160 {_26795 : Type'} (n : nat) (x : _26795) : (term43 _26795 n x) = (term44 _26795 n x).
Proof. exact (@lem1138159 _26795 n x). Qed.
Lemma lem1138161 {_26795 : Type'} : (@List.length _26795) = (@List.length _26795).
Proof. exact (eq_refl (@List.length _26795)). Qed.
Lemma lem1138162 {_26795 : Type'} (n : nat) (x : _26795) : (term45 _26795 n x) = (term46 _26795 n x).
Proof. exact (MK_COMB (@lem1138161 _26795) (@lem1138160 _26795 n x)). Qed.
Lemma lem1138164 {A : Type'} (h : A) (t : list A) : (term39 A h t) = (term40 A t).
Proof. exact (EQ_MP (@lem1138146 A h t) (@lem1138145 A h t)). Qed.
Lemma lem1138165 {_26795 : Type'} (h : _26795) (t : list _26795) : (term39 _26795 h t) = (term40 _26795 t).
Proof. exact (@lem1138164 _26795 h t). Qed.
Lemma lem1138166 {_26795 : Type'} (n : nat) (x : _26795) : (term46 _26795 n x) = (term47 _26795 n x).
Proof. exact (@lem1138165 _26795 x (@repeat_with_perm_args _26795 n x)). Qed.
Lemma lem1138168 {_26795 : Type'} (x : _26795) (n : nat) (h1 : term8 _26795 n) : (term42 _26795 n x) = n.
Proof. exact (EQ_MP (@lem1138150 _26795 x n) (@lem1138149 _26795 x n h1)). Qed.
Lemma lem1138169 {_26795 : Type'} (x : _26795) (n : nat) (h1 : term8 _26795 n) : (term42 _26795 n x) = n.
Proof. exact (@lem1138168 _26795 x n h1). Qed.
Lemma lem1138170 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem1138171 {_26795 : Type'} (x : _26795) (n : nat) (h1 : term8 _26795 n) : (term47 _26795 n x) = (S n).
Proof. exact (MK_COMB (@lem1138170) (@lem1138169 _26795 x n h1)). Qed.
Lemma lem1138172 {_26795 : Type'} (x : _26795) (n : nat) (h1 : term8 _26795 n) : (term46 _26795 n x) = (S n).
Proof. exact (TRANS (@lem1138166 _26795 n x) (@lem1138171 _26795 x n h1)). Qed.
Lemma lem1138173 {_26795 : Type'} (x : _26795) (n : nat) (h1 : term8 _26795 n) : (term45 _26795 n x) = (S n).
Proof. exact (TRANS (@lem1138162 _26795 n x) (@lem1138172 _26795 x n h1)). Qed.
Lemma lem1138174 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1138175 {_26795 : Type'} (x : _26795) (n : nat) (h1 : term8 _26795 n) : (term48 _26795 n x) = (term49 n).
Proof. exact (MK_COMB (@lem1138174) (@lem1138173 _26795 x n h1)). Qed.
Lemma lem1138176 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem1138177 {_26795 : Type'} (x : _26795) (n : nat) (h1 : term8 _26795 n) : ((term45 _26795 n x) = (S n)) = ((S n) = (S n)).
Proof. exact (MK_COMB (@lem1138175 _26795 x n h1) (@lem1138176 n)). Qed.
Lemma lem1138179 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1138180 (x : nat) : (x = x) = True.
Proof. exact (@lem1138179 nat x). Qed.
Lemma lem1138181 (n : nat) : ((S n) = (S n)) = True.
Proof. exact (@lem1138180 (S n)). Qed.
Lemma lem1138182 {_26795 : Type'} (x : _26795) (n : nat) (h1 : term8 _26795 n) : ((term45 _26795 n x) = (S n)) = True.
Proof. exact (TRANS (@lem1138177 _26795 x n h1) (@lem1138181 n)). Qed.
Lemma lem1138183 {_26795 : Type'} (n : nat) (h1 : term8 _26795 n) : (term50 _26795 n) = (term32 _26795).
Proof. exact (fun_ext (fun x : _26795 => @lem1138182 _26795 x n h1)). Qed.
Lemma lem1138184 {_26795 : Type'} : (@all _26795) = (@all _26795).
Proof. exact (eq_refl (@all _26795)). Qed.
Lemma lem1138185 {_26795 : Type'} (n : nat) (h1 : term8 _26795 n) : (term12 _26795 n) = (term33 _26795).
Proof. exact (MK_COMB (@lem1138184 _26795) (@lem1138183 _26795 n h1)). Qed.
Lemma lem1138187 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1138188 {_26795 : Type'} (t : Prop) : (term34 _26795 t) = t.
Proof. exact (@lem1138187 _26795 t). Qed.
Lemma lem1138189 {_26795 : Type'} : (term33 _26795) = True.
Proof. exact (@lem1138188 _26795 True). Qed.
Lemma lem1138190 {_26795 : Type'} (n : nat) (h1 : term8 _26795 n) : (term12 _26795 n) = True.
Proof. exact (TRANS (@lem1138185 _26795 n h1) (@lem1138189 _26795)). Qed.
Lemma lem1138191 {_26795 : Type'} (n : nat) (h1 : term8 _26795 n) : True = (term12 _26795 n).
Proof. exact (SYM (@lem1138190 _26795 n h1)). Qed.
Lemma lem1138192 {_26795 : Type'} (n : nat) (h1 : term8 _26795 n) : term12 _26795 n.
Proof. exact (EQ_MP (@lem1138191 _26795 n h1) (@lem0)). Qed.
Lemma lem1138193 {_26795 : Type'} (n : nat) : term14 _26795 n.
Proof. exact (fun h0 : term8 _26795 n => @lem1138192 _26795 n h0). Qed.
Lemma lem1138198 {_26795 : Type'} : term18 _26795.
Proof. exact (fun n : nat => @lem1138193 _26795 n). Qed.
Lemma lem1138199 {_26795 : Type'} : term20 _26795.
Proof. exact (conj (@lem1138138 _26795) (@lem1138198 _26795)). Qed.
Lemma lem1138200 {_26795 : Type'} : term25 _26795.
Proof. exact (@lem1138093 _26795 (@lem1138199 _26795)). Qed.
