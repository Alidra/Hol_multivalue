Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_SUB_NUMSEG_term_abbrevs.
Require Import FINITE_NUMSEG_spec.
Require Import SUM_SUB_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem7210116 (m : nat) : term0 m.
Proof. exact (@lem5329299 m). Qed.
Lemma lem7210117 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem7210118 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem7210117 m) (@lem7210116 m)). Qed.
Lemma lem7210119 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem7210118 m n). Qed.
Lemma lem7210120 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem7210121 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem7210120 m n) (@lem7210119 m n)). Qed.
Lemma lem7210122 (m : nat) (n : nat) : (term3 m n) = ((term3 m n) = True).
Proof. exact (@lem7 (term3 m n)). Qed.
Lemma lem7210124 {_132039 : Type'} (f : _132039 -> real) : term4 _132039 f.
Proof. exact (@lem7071000 _132039 f). Qed.
Lemma lem7210125 {_132039 : Type'} (f : _132039 -> real) : (term4 _132039 f) = (term5 _132039 f).
Proof. exact (eq_refl (term4 _132039 f)). Qed.
Lemma lem7210126 {_132039 : Type'} (f : _132039 -> real) : term5 _132039 f.
Proof. exact (EQ_MP (@lem7210125 _132039 f) (@lem7210124 _132039 f)). Qed.
Lemma lem7210127 {_132039 : Type'} (f : _132039 -> real) (g : _132039 -> real) : term6 _132039 f g.
Proof. exact (@lem7210126 _132039 f g). Qed.
Lemma lem7210128 {_132039 : Type'} (f : _132039 -> real) (g : _132039 -> real) : (term6 _132039 f g) = (term7 _132039 f g).
Proof. exact (eq_refl (term6 _132039 f g)). Qed.
Lemma lem7210129 {_132039 : Type'} (f : _132039 -> real) (g : _132039 -> real) : term7 _132039 f g.
Proof. exact (EQ_MP (@lem7210128 _132039 f g) (@lem7210127 _132039 f g)). Qed.
Lemma lem7210130 {_132039 : Type'} (f : _132039 -> real) (g : _132039 -> real) (s : _132039 -> Prop) : term8 _132039 f g s.
Proof. exact (@lem7210129 _132039 f g s). Qed.
Lemma lem7210131 {_132039 : Type'} (f : _132039 -> real) (s : _132039 -> Prop) (g : _132039 -> real) : (term8 _132039 f g s) = (term9 _132039 f s g).
Proof. exact (eq_refl (term8 _132039 f g s)). Qed.
Lemma lem7210132 {_132039 : Type'} (f : _132039 -> real) (s : _132039 -> Prop) (g : _132039 -> real) : term9 _132039 f s g.
Proof. exact (EQ_MP (@lem7210131 _132039 f s g) (@lem7210130 _132039 f g s)). Qed.
Lemma lem7210133 {_132039 : Type'} (s : _132039 -> Prop) (h1 : @FINITE _132039 s) : @FINITE _132039 s.
Proof. exact (h1). Qed.
Lemma lem7210134 {_132039 : Type'} (f : _132039 -> real) (g : _132039 -> real) (s : _132039 -> Prop) (h1 : @FINITE _132039 s) : (term10 _132039 s f g) = (term11 _132039 f s g).
Proof. exact (@lem7210132 _132039 f s g (@lem7210133 _132039 s h1)). Qed.
Lemma lem7210159 {_132039 : Type'} (f : _132039 -> real) (s : _132039 -> Prop) (g : _132039 -> real) : term9 _132039 f s g.
Proof. exact (fun h0 : @FINITE _132039 s => @lem7210134 _132039 f g s h0). Qed.
Lemma lem7210160 (f : nat -> real) (s : nat -> Prop) (g : nat -> real) : term12 f s g.
Proof. exact (@lem7210159 nat f s g). Qed.
Lemma lem7210161 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : term13 f m n g.
Proof. exact (@lem7210160 f (dotdot m n) g). Qed.
Lemma lem7210163 (m : nat) (n : nat) : (term3 m n) = True.
Proof. exact (EQ_MP (@lem7210122 m n) (@lem7210121 m n)). Qed.
Lemma lem7210164 (m : nat) (n : nat) : True = (term3 m n).
Proof. exact (SYM (@lem7210163 m n)). Qed.
Lemma lem7210165 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem7210164 m n) (@lem0)). Qed.
Lemma lem7210166 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : (term14 m n f g) = (term15 f m n g).
Proof. exact (@lem7210161 f m n g (@lem7210165 m n)). Qed.
Lemma lem7210167 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7210168 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : (term16 m n f g) = (term17 f m n g).
Proof. exact (MK_COMB (@lem7210167) (@lem7210166 f m n g)). Qed.
Lemma lem7210169 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : (term15 f m n g) = (term15 f m n g).
Proof. exact (eq_refl (term15 f m n g)). Qed.
Lemma lem7210170 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : ((term14 m n f g) = (term15 f m n g)) = ((term15 f m n g) = (term15 f m n g)).
Proof. exact (MK_COMB (@lem7210168 f m n g) (@lem7210169 f m n g)). Qed.
Lemma lem7210172 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7210173 (x : real) : (x = x) = True.
Proof. exact (@lem7210172 real x). Qed.
Lemma lem7210174 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : ((term15 f m n g) = (term15 f m n g)) = True.
Proof. exact (@lem7210173 (term15 f m n g)). Qed.
Lemma lem7210175 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : ((term14 m n f g) = (term15 f m n g)) = True.
Proof. exact (TRANS (@lem7210170 f m n g) (@lem7210174 f m n g)). Qed.
Lemma lem7210176 (f : nat -> real) (m : nat) (g : nat -> real) : (term18 f m g) = term19.
Proof. exact (fun_ext (fun n : nat => @lem7210175 f m n g)). Qed.
Lemma lem7210177 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7210178 (f : nat -> real) (m : nat) (g : nat -> real) : (term20 f m g) = term21.
Proof. exact (MK_COMB (@lem7210177) (@lem7210176 f m g)). Qed.
Lemma lem7210180 {A : Type'} (t : Prop) : (term22 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7210181 (t : Prop) : (term23 t) = t.
Proof. exact (@lem7210180 nat t). Qed.
Lemma lem7210182 : term21 = True.
Proof. exact (@lem7210181 True). Qed.
Lemma lem7210183 (f : nat -> real) (m : nat) (g : nat -> real) : (term20 f m g) = True.
Proof. exact (TRANS (@lem7210178 f m g) (@lem7210182)). Qed.
Lemma lem7210184 (f : nat -> real) (g : nat -> real) : (term24 f g) = term19.
Proof. exact (fun_ext (fun m : nat => @lem7210183 f m g)). Qed.
Lemma lem7210185 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7210186 (f : nat -> real) (g : nat -> real) : (term25 f g) = term21.
Proof. exact (MK_COMB (@lem7210185) (@lem7210184 f g)). Qed.
Lemma lem7210188 {A : Type'} (t : Prop) : (term22 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7210189 (t : Prop) : (term23 t) = t.
Proof. exact (@lem7210188 nat t). Qed.
Lemma lem7210190 : term21 = True.
Proof. exact (@lem7210189 True). Qed.
Lemma lem7210191 (f : nat -> real) (g : nat -> real) : (term25 f g) = True.
Proof. exact (TRANS (@lem7210186 f g) (@lem7210190)). Qed.
Lemma lem7210192 (f : nat -> real) : (term26 f) = term27.
Proof. exact (fun_ext (fun g : nat -> real => @lem7210191 f g)). Qed.
Lemma lem7210193 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7210194 (f : nat -> real) : (term28 f) = term29.
Proof. exact (MK_COMB (@lem7210193) (@lem7210192 f)). Qed.
Lemma lem7210196 {A : Type'} (t : Prop) : (term22 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7210197 (t : Prop) : (term30 t) = t.
Proof. exact (@lem7210196 (nat -> real) t). Qed.
Lemma lem7210198 : term29 = True.
Proof. exact (@lem7210197 True). Qed.
Lemma lem7210199 (f : nat -> real) : (term28 f) = True.
Proof. exact (TRANS (@lem7210194 f) (@lem7210198)). Qed.
Lemma lem7210200 : term31 = term27.
Proof. exact (fun_ext (fun f : nat -> real => @lem7210199 f)). Qed.
Lemma lem7210201 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7210202 : term32 = term29.
Proof. exact (MK_COMB (@lem7210201) (@lem7210200)). Qed.
Lemma lem7210204 {A : Type'} (t : Prop) : (term22 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7210205 (t : Prop) : (term30 t) = t.
Proof. exact (@lem7210204 (nat -> real) t). Qed.
Lemma lem7210206 : term29 = True.
Proof. exact (@lem7210205 True). Qed.
Lemma lem7210207 : term32 = True.
Proof. exact (TRANS (@lem7210202) (@lem7210206)). Qed.
Lemma lem7210208 : True = term32.
Proof. exact (SYM (@lem7210207)). Qed.
Lemma lem7210209 : term32.
Proof. exact (EQ_MP (@lem7210208) (@lem0)). Qed.
