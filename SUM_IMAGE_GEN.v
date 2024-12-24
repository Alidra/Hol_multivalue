Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_IMAGE_GEN_term_abbrevs.
Require Import ITERATE_IMAGE_GEN_spec.
Require Import MONOIDAL_REAL_ADD_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Require Import thm7064097_spec.
Require Import thm7064111_spec.
Lemma lem7159144 : (@monoidal real real_add) = ((@monoidal real real_add) = True).
Proof. exact (@lem7 (@monoidal real real_add)). Qed.
Lemma lem7159146 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (h1). Qed.
Lemma lem7159147 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term1 A B C op.
Proof. exact (@lem7159146 A B C h1 op). Qed.
Lemma lem7159148 {A B C : Type'} (op : type1400 C) : (term1 A B C op) = (term2 A B C op).
Proof. exact (eq_refl (term1 A B C op)). Qed.
Lemma lem7159149 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term2 A B C op.
Proof. exact (EQ_MP (@lem7159148 A B C op) (@lem7159147 A B C op h1)). Qed.
Lemma lem7159150 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @monoidal C op.
Proof. exact (h1). Qed.
Lemma lem7159151 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) (h2 : @monoidal C op) : term3 A B C op.
Proof. exact (@lem7159149 A B C op h1 (@lem7159150 C op h2)). Qed.
Lemma lem7159152 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term4 A B C op.
Proof. exact (fun h0 : term0 A B C => @lem7159151 A B C op h0 h1). Qed.
Lemma lem7159153 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (h1). Qed.
Lemma lem7159154 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) (h2 : @monoidal C op) : term3 A B C op.
Proof. exact (@lem7159152 A B C op h2 (@lem7159153 A B C h1)). Qed.
Lemma lem7159155 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term2 A B C op.
Proof. exact (fun h0 : @monoidal C op => @lem7159154 A B C op h1 h0). Qed.
Lemma lem7159156 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (fun op : type1400 C => @lem7159155 A B C op h1). Qed.
Lemma lem7159157 {A B C : Type'} : term5 A B C.
Proof. exact (fun h0 : term0 A B C => @lem7159156 A B C h0). Qed.
Lemma lem7159158 {A B C : Type'} : term0 A B C.
Proof. exact (@lem7159157 A B C (@lem6158399 A B C)). Qed.
Lemma lem7159159 {A B C : Type'} (op : type1400 C) : term1 A B C op.
Proof. exact (@lem7159158 A B C op). Qed.
Lemma lem7159160 {A B C : Type'} (op : type1400 C) : (term1 A B C op) = (term2 A B C op).
Proof. exact (eq_refl (term1 A B C op)). Qed.
Lemma lem7159179 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7159180 {A : Type'} : (@sum A) = (@iterate real A real_add).
Proof. exact (@lem7159179 A). Qed.
Lemma lem7159181 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7159182 {A : Type'} (s : A -> Prop) : (@sum A s) = (@iterate real A real_add s).
Proof. exact (MK_COMB (@lem7159180 A) (@lem7159181 A s)). Qed.
Lemma lem7159183 {A : Type'} (g : A -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7159184 {A : Type'} (s : A -> Prop) (g : A -> real) : (@sum A s g) = (@iterate real A real_add s g).
Proof. exact (MK_COMB (@lem7159182 A s) (@lem7159183 A g)). Qed.
Lemma lem7159185 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7159186 {A : Type'} (s : A -> Prop) (g : A -> real) : (term6 A s g) = (term7 A s g).
Proof. exact (MK_COMB (@lem7159185) (@lem7159184 A s g)). Qed.
Lemma lem7159188 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7159189 {B : Type'} : (@sum B) = (@iterate real B real_add).
Proof. exact (@lem7159188 B). Qed.
Lemma lem7159190 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (@IMAGE A B f s).
Proof. exact (eq_refl (@IMAGE A B f s)). Qed.
Lemma lem7159191 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term8 A B f s) = (term9 A B f s).
Proof. exact (MK_COMB (@lem7159189 B) (@lem7159190 A B f s)). Qed.
Lemma lem7159193 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7159194 {A : Type'} : (@sum A) = (@iterate real A real_add).
Proof. exact (@lem7159193 A). Qed.
Lemma lem7159203 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term10 A B s f y) = (term10 A B s f y).
Proof. exact (eq_refl (term10 A B s f y)). Qed.
Lemma lem7159204 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term11 A B s f y) = (term12 A B s f y).
Proof. exact (MK_COMB (@lem7159194 A) (@lem7159203 A B s f y)). Qed.
Lemma lem7159205 {A : Type'} (g : A -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7159206 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (g : A -> real) : (term13 A B s f y g) = (term14 A B s f y g).
Proof. exact (MK_COMB (@lem7159204 A B s f y) (@lem7159205 A g)). Qed.
Lemma lem7159207 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> real) : (term15 A B s f g) = (term16 A B s f g).
Proof. exact (fun_ext (fun y : B => @lem7159206 A B s f y g)). Qed.
Lemma lem7159208 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> real) : (term17 A B s f g) = (term18 A B s f g).
Proof. exact (MK_COMB (@lem7159191 A B f s) (@lem7159207 A B s f g)). Qed.
Lemma lem7159209 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> real) : ((@sum A s g) = (term17 A B s f g)) = ((@iterate real A real_add s g) = (term18 A B s f g)).
Proof. exact (MK_COMB (@lem7159186 A s g) (@lem7159208 A B s f g)). Qed.
Lemma lem7159212 {A : Type'} (s : A -> Prop) : (term19 A s) = (term19 A s).
Proof. exact (eq_refl (term19 A s)). Qed.
Lemma lem7159213 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> real) : (term20 A B s f g) = (term21 A B s f g).
Proof. exact (MK_COMB (@lem7159212 A s) (@lem7159209 A B s f g)). Qed.
Lemma lem7159216 {A B : Type'} (f : A -> B) (g : A -> real) : (term22 A B f g) = (term23 A B f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7159213 A B s f g)). Qed.
Lemma lem7159217 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7159218 {A B : Type'} (f : A -> B) (g : A -> real) : (term24 A B f g) = (term25 A B f g).
Proof. exact (MK_COMB (@lem7159217 A) (@lem7159216 A B f g)). Qed.
Lemma lem7159223 {A B : Type'} (f : A -> B) : (term26 A B f) = (term27 A B f).
Proof. exact (fun_ext (fun g : A -> real => @lem7159218 A B f g)). Qed.
Lemma lem7159224 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7159225 {A B : Type'} (f : A -> B) : (term28 A B f) = (term29 A B f).
Proof. exact (MK_COMB (@lem7159224 A) (@lem7159223 A B f)). Qed.
Lemma lem7159230 {A B : Type'} : (term30 A B) = (term31 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem7159225 A B f)). Qed.
Lemma lem7159231 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem7159232 {A B : Type'} : (term32 A B) = (term33 A B).
Proof. exact (MK_COMB (@lem7159231 A B) (@lem7159230 A B)). Qed.
Lemma lem7159237 {A B : Type'} : (term33 A B) = (term32 A B).
Proof. exact (SYM (@lem7159232 A B)). Qed.
Lemma lem7159239 {A B C : Type'} (op : type1400 C) : term2 A B C op.
Proof. exact (EQ_MP (@lem7159160 A B C op) (@lem7159159 A B C op)). Qed.
Lemma lem7159240 {A B : Type'} (op : type1627) : term34 A B op.
Proof. exact (@lem7159239 A B real op). Qed.
Lemma lem7159241 {A B : Type'} : term35 A B.
Proof. exact (@lem7159240 A B real_add). Qed.
Lemma lem7159243 : (@monoidal real real_add) = True.
Proof. exact (EQ_MP (@lem7159144) (@lem7067132)). Qed.
Lemma lem7159244 : True = (@monoidal real real_add).
Proof. exact (SYM (@lem7159243)). Qed.
Lemma lem7159245 : @monoidal real real_add.
Proof. exact (EQ_MP (@lem7159244) (@lem0)). Qed.
Lemma lem7159246 {A B : Type'} : term33 A B.
Proof. exact (@lem7159241 A B (@lem7159245)). Qed.
Lemma lem7159247 {A B : Type'} : term32 A B.
Proof. exact (EQ_MP (@lem7159237 A B) (@lem7159246 A B)). Qed.
