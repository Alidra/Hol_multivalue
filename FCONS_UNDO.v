Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FCONS_UNDO_term_abbrevs.
Require Import FUN_EQ_THM_spec.
Require Import o_THM_spec.
Require Import thm0_spec.
Require Import thm1066089_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem1066093 {A B C : Type'} (f : B -> C) : term0 A B C f.
Proof. exact (@lem15456 A B C f). Qed.
Lemma lem1066094 {A B C : Type'} (f : B -> C) : (term0 A B C f) = (term1 A B C f).
Proof. exact (eq_refl (term0 A B C f)). Qed.
Lemma lem1066095 {A B C : Type'} (f : B -> C) : term1 A B C f.
Proof. exact (EQ_MP (@lem1066094 A B C f) (@lem1066093 A B C f)). Qed.
Lemma lem1066096 {A B C : Type'} (f : B -> C) (g : A -> B) : term2 A B C f g.
Proof. exact (@lem1066095 A B C f g). Qed.
Lemma lem1066097 {A B C : Type'} (f : B -> C) (g : A -> B) : (term2 A B C f g) = (term3 A B C f g).
Proof. exact (eq_refl (term2 A B C f g)). Qed.
Lemma lem1066098 {A B C : Type'} (f : B -> C) (g : A -> B) : term3 A B C f g.
Proof. exact (EQ_MP (@lem1066097 A B C f g) (@lem1066096 A B C f g)). Qed.
Lemma lem1066099 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : term4 A B C f g x.
Proof. exact (@lem1066098 A B C f g x). Qed.
Lemma lem1066100 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (term4 A B C f g x) = ((@o A B C f g x) = (term5 A B C f g x)).
Proof. exact (eq_refl (term4 A B C f g x)). Qed.
Lemma lem1066102 {A : Type'} : term6 A.
Proof. exact (proj2 (@lem1066089 A)). Qed.
Lemma lem1066103 {A : Type'} (a : A) : term7 A a.
Proof. exact (@lem1066102 A a). Qed.
Lemma lem1066104 {A : Type'} (a : A) : (term7 A a) = (term8 A a).
Proof. exact (eq_refl (term7 A a)). Qed.
Lemma lem1066105 {A : Type'} (a : A) : term8 A a.
Proof. exact (EQ_MP (@lem1066104 A a) (@lem1066103 A a)). Qed.
Lemma lem1066106 {A : Type'} (a : A) (f : nat -> A) : term9 A a f.
Proof. exact (@lem1066105 A a f). Qed.
Lemma lem1066107 {A : Type'} (a : A) (f : nat -> A) : (term9 A a f) = (term10 A a f).
Proof. exact (eq_refl (term9 A a f)). Qed.
Lemma lem1066108 {A : Type'} (a : A) (f : nat -> A) : term10 A a f.
Proof. exact (EQ_MP (@lem1066107 A a f) (@lem1066106 A a f)). Qed.
Lemma lem1066109 {A : Type'} (a : A) (f : nat -> A) (n : nat) : term11 A a f n.
Proof. exact (@lem1066108 A a f n). Qed.
Lemma lem1066110 {A : Type'} (a : A) (f : nat -> A) (n : nat) : (term11 A a f n) = ((term12 A a f n) = (f n)).
Proof. exact (eq_refl (term11 A a f n)). Qed.
Lemma lem1066112 {A : Type'} : term13 A.
Proof. exact (proj1 (@lem1066089 A)). Qed.
Lemma lem1066113 {A : Type'} (a : A) : term14 A a.
Proof. exact (@lem1066112 A a). Qed.
Lemma lem1066114 {A : Type'} (a : A) : (term14 A a) = (term15 A a).
Proof. exact (eq_refl (term14 A a)). Qed.
Lemma lem1066115 {A : Type'} (a : A) : term15 A a.
Proof. exact (EQ_MP (@lem1066114 A a) (@lem1066113 A a)). Qed.
Lemma lem1066116 {A : Type'} (a : A) (f : nat -> A) : term16 A a f.
Proof. exact (@lem1066115 A a f). Qed.
Lemma lem1066117 {A : Type'} (f : nat -> A) (a : A) : (term16 A a f) = ((term17 A a f) = a).
Proof. exact (eq_refl (term16 A a f)). Qed.
Lemma lem1066119 {A B : Type'} (f : A -> B) : term18 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem1066120 {A B : Type'} (f : A -> B) : (term18 A B f) = (term19 A B f).
Proof. exact (eq_refl (term18 A B f)). Qed.
Lemma lem1066121 {A B : Type'} (f : A -> B) : term19 A B f.
Proof. exact (EQ_MP (@lem1066120 A B f) (@lem1066119 A B f)). Qed.
Lemma lem1066122 {A B : Type'} (f : A -> B) (g : A -> B) : term20 A B f g.
Proof. exact (@lem1066121 A B f g). Qed.
Lemma lem1066123 {A B : Type'} (f : A -> B) (g : A -> B) : (term20 A B f g) = ((f = g) = (term21 A B f g)).
Proof. exact (eq_refl (term20 A B f g)). Qed.
Lemma lem1066128 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term21 A B f g).
Proof. exact (EQ_MP (@lem1066123 A B f g) (@lem1066122 A B f g)). Qed.
Lemma lem1066129 {A : Type'} (f : nat -> A) (g : nat -> A) : (f = g) = (term22 A f g).
Proof. exact (@lem1066128 nat A f g). Qed.
Lemma lem1066130 {A : Type'} (f : nat -> A) : (f = (term23 A f)) = (term24 A f).
Proof. exact (@lem1066129 A f (term23 A f)). Qed.
Lemma lem1066139 {A : Type'} (f : nat -> A) : (term24 A f) = (f = (term23 A f)).
Proof. exact (SYM (@lem1066130 A f)). Qed.
Lemma lem1066141 (P : nat -> Prop) : term25 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1066142 {A : Type'} (f : nat -> A) : term26 A f.
Proof. exact (@lem1066141 (term27 A f)). Qed.
Lemma lem1066143 {A : Type'} (f : nat -> A) : (term28 A f) = ((term29 A f) = (term30 A f)).
Proof. exact (eq_refl (term28 A f)). Qed.
Lemma lem1066144 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1066145 {A : Type'} (f : nat -> A) : (term31 A f) = (term32 A f).
Proof. exact (MK_COMB (@lem1066144) (@lem1066143 A f)). Qed.
Lemma lem1066146 {A : Type'} (f : nat -> A) (x : nat) : (term33 A f x) = ((f x) = (term34 A f x)).
Proof. exact (eq_refl (term33 A f x)). Qed.
Lemma lem1066147 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1066148 {A : Type'} (f : nat -> A) (x : nat) : (term35 A f x) = (term36 A f x).
Proof. exact (MK_COMB (@lem1066147) (@lem1066146 A f x)). Qed.
Lemma lem1066149 {A : Type'} (f : nat -> A) (x : nat) : (term37 A f x) = ((term38 A f x) = (term39 A f x)).
Proof. exact (eq_refl (term37 A f x)). Qed.
Lemma lem1066150 {A : Type'} (f : nat -> A) (x : nat) : (term40 A f x) = (term41 A f x).
Proof. exact (MK_COMB (@lem1066148 A f x) (@lem1066149 A f x)). Qed.
Lemma lem1066151 {A : Type'} (f : nat -> A) : (term42 A f) = (term43 A f).
Proof. exact (fun_ext (fun x : nat => @lem1066150 A f x)). Qed.
Lemma lem1066152 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1066153 {A : Type'} (f : nat -> A) : (term44 A f) = (term45 A f).
Proof. exact (MK_COMB (@lem1066152) (@lem1066151 A f)). Qed.
Lemma lem1066154 {A : Type'} (f : nat -> A) : (term46 A f) = (term47 A f).
Proof. exact (MK_COMB (@lem1066145 A f) (@lem1066153 A f)). Qed.
Lemma lem1066155 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1066156 {A : Type'} (f : nat -> A) : (term48 A f) = (term49 A f).
Proof. exact (MK_COMB (@lem1066155) (@lem1066154 A f)). Qed.
Lemma lem1066157 {A : Type'} (f : nat -> A) (x : nat) : (term33 A f x) = ((f x) = (term34 A f x)).
Proof. exact (eq_refl (term33 A f x)). Qed.
Lemma lem1066158 {A : Type'} (f : nat -> A) : (term50 A f) = (term27 A f).
Proof. exact (fun_ext (fun x : nat => @lem1066157 A f x)). Qed.
Lemma lem1066159 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1066160 {A : Type'} (f : nat -> A) : (term51 A f) = (term24 A f).
Proof. exact (MK_COMB (@lem1066159) (@lem1066158 A f)). Qed.
Lemma lem1066161 {A : Type'} (f : nat -> A) : (term26 A f) = (term52 A f).
Proof. exact (MK_COMB (@lem1066156 A f) (@lem1066160 A f)). Qed.
Lemma lem1066162 {A : Type'} (f : nat -> A) : term52 A f.
Proof. exact (EQ_MP (@lem1066161 A f) (@lem1066142 A f)). Qed.
Lemma lem1066167 {A : Type'} (f : nat -> A) (a : A) : (term17 A a f) = a.
Proof. exact (EQ_MP (@lem1066117 A f a) (@lem1066116 A a f)). Qed.
Lemma lem1066168 {A : Type'} (f : nat -> A) (a : A) : (term17 A a f) = a.
Proof. exact (@lem1066167 A f a). Qed.
Lemma lem1066169 {A : Type'} (f : nat -> A) : (term30 A f) = (term29 A f).
Proof. exact (@lem1066168 A (@o nat nat A f S) (term29 A f)). Qed.
Lemma lem1066170 {A : Type'} (f : nat -> A) : (term53 A f) = (term53 A f).
Proof. exact (eq_refl (term53 A f)). Qed.
Lemma lem1066171 {A : Type'} (f : nat -> A) : ((term29 A f) = (term30 A f)) = ((term29 A f) = (term29 A f)).
Proof. exact (MK_COMB (@lem1066170 A f) (@lem1066169 A f)). Qed.
Lemma lem1066173 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1066174 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1066173 A x). Qed.
Lemma lem1066175 {A : Type'} (f : nat -> A) : ((term29 A f) = (term29 A f)) = True.
Proof. exact (@lem1066174 A (term29 A f)). Qed.
Lemma lem1066176 {A : Type'} (f : nat -> A) : ((term29 A f) = (term30 A f)) = True.
Proof. exact (TRANS (@lem1066171 A f) (@lem1066175 A f)). Qed.
Lemma lem1066177 {A : Type'} (f : nat -> A) : True = ((term29 A f) = (term30 A f)).
Proof. exact (SYM (@lem1066176 A f)). Qed.
Lemma lem1066178 {A : Type'} (f : nat -> A) : (term29 A f) = (term30 A f).
Proof. exact (EQ_MP (@lem1066177 A f) (@lem0)). Qed.
Lemma lem1066182 {A : Type'} (a : A) (f : nat -> A) (n : nat) : (term12 A a f n) = (f n).
Proof. exact (EQ_MP (@lem1066110 A a f n) (@lem1066109 A a f n)). Qed.
Lemma lem1066183 {A : Type'} (a : A) (f : nat -> A) (n : nat) : (term12 A a f n) = (f n).
Proof. exact (@lem1066182 A a f n). Qed.
Lemma lem1066184 {A : Type'} (f : nat -> A) (x : nat) : (term39 A f x) = (@o nat nat A f S x).
Proof. exact (@lem1066183 A (term29 A f) (@o nat nat A f S) x). Qed.
Lemma lem1066186 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (@o A B C f g x) = (term5 A B C f g x).
Proof. exact (EQ_MP (@lem1066100 A B C f g x) (@lem1066099 A B C f g x)). Qed.
Lemma lem1066187 {A : Type'} (f : nat -> A) (g : nat -> nat) (x : nat) : (@o nat nat A f g x) = (term54 A f g x).
Proof. exact (@lem1066186 nat nat A f g x). Qed.
Lemma lem1066188 {A : Type'} (f : nat -> A) (x : nat) : (@o nat nat A f S x) = (term38 A f x).
Proof. exact (@lem1066187 A f S x). Qed.
Lemma lem1066189 {A : Type'} (f : nat -> A) (x : nat) : (term39 A f x) = (term38 A f x).
Proof. exact (TRANS (@lem1066184 A f x) (@lem1066188 A f x)). Qed.
Lemma lem1066190 {A : Type'} (f : nat -> A) (x : nat) : (term55 A f x) = (term55 A f x).
Proof. exact (eq_refl (term55 A f x)). Qed.
Lemma lem1066191 {A : Type'} (f : nat -> A) (x : nat) : ((term38 A f x) = (term39 A f x)) = ((term38 A f x) = (term38 A f x)).
Proof. exact (MK_COMB (@lem1066190 A f x) (@lem1066189 A f x)). Qed.
Lemma lem1066193 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1066194 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1066193 A x). Qed.
Lemma lem1066195 {A : Type'} (f : nat -> A) (x : nat) : ((term38 A f x) = (term38 A f x)) = True.
Proof. exact (@lem1066194 A (term38 A f x)). Qed.
Lemma lem1066196 {A : Type'} (f : nat -> A) (x : nat) : ((term38 A f x) = (term39 A f x)) = True.
Proof. exact (TRANS (@lem1066191 A f x) (@lem1066195 A f x)). Qed.
Lemma lem1066197 {A : Type'} (f : nat -> A) (x : nat) : True = ((term38 A f x) = (term39 A f x)).
Proof. exact (SYM (@lem1066196 A f x)). Qed.
Lemma lem1066198 {A : Type'} (f : nat -> A) (x : nat) : (term38 A f x) = (term39 A f x).
Proof. exact (EQ_MP (@lem1066197 A f x) (@lem0)). Qed.
Lemma lem1066199 {A : Type'} (f : nat -> A) (x : nat) : term41 A f x.
Proof. exact (fun h0 : (f x) = (term34 A f x) => @lem1066198 A f x). Qed.
Lemma lem1066204 {A : Type'} (f : nat -> A) : term45 A f.
Proof. exact (fun x : nat => @lem1066199 A f x). Qed.
Lemma lem1066205 {A : Type'} (f : nat -> A) : term47 A f.
Proof. exact (conj (@lem1066178 A f) (@lem1066204 A f)). Qed.
Lemma lem1066206 {A : Type'} (f : nat -> A) : term24 A f.
Proof. exact (@lem1066162 A f (@lem1066205 A f)). Qed.
Lemma lem1066207 {A : Type'} (f : nat -> A) : f = (term23 A f).
Proof. exact (EQ_MP (@lem1066139 A f) (@lem1066206 A f)). Qed.
Lemma lem1066212 {A : Type'} : term56 A.
Proof. exact (fun f : nat -> A => @lem1066207 A f). Qed.
