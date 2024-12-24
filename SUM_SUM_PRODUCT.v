Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_SUM_PRODUCT_term_abbrevs.
Require Import ITERATE_ITERATE_PRODUCT_spec.
Require Import MONOIDAL_REAL_ADD_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Require Import thm7064097_spec.
Require Import thm7064111_spec.
Lemma lem7178146 : (@monoidal real real_add) = ((@monoidal real real_add) = True).
Proof. exact (@lem7 (@monoidal real real_add)). Qed.
Lemma lem7178148 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (h1). Qed.
Lemma lem7178149 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term1 A B C op.
Proof. exact (@lem7178148 A B C h1 op). Qed.
Lemma lem7178150 {A B C : Type'} (op : type1400 C) : (term1 A B C op) = (term2 A B C op).
Proof. exact (eq_refl (term1 A B C op)). Qed.
Lemma lem7178151 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term2 A B C op.
Proof. exact (EQ_MP (@lem7178150 A B C op) (@lem7178149 A B C op h1)). Qed.
Lemma lem7178152 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @monoidal C op.
Proof. exact (h1). Qed.
Lemma lem7178153 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) (h2 : @monoidal C op) : term3 A B C op.
Proof. exact (@lem7178151 A B C op h1 (@lem7178152 C op h2)). Qed.
Lemma lem7178154 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term4 A B C op.
Proof. exact (fun h0 : term0 A B C => @lem7178153 A B C op h0 h1). Qed.
Lemma lem7178155 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (h1). Qed.
Lemma lem7178156 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) (h2 : @monoidal C op) : term3 A B C op.
Proof. exact (@lem7178154 A B C op h2 (@lem7178155 A B C h1)). Qed.
Lemma lem7178157 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term2 A B C op.
Proof. exact (fun h0 : @monoidal C op => @lem7178156 A B C op h1 h0). Qed.
Lemma lem7178158 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (fun op : type1400 C => @lem7178157 A B C op h1). Qed.
Lemma lem7178159 {A B C : Type'} : term5 A B C.
Proof. exact (fun h0 : term0 A B C => @lem7178158 A B C h0). Qed.
Lemma lem7178160 {A B C : Type'} : term0 A B C.
Proof. exact (@lem7178159 A B C (@lem5970042 A B C)). Qed.
Lemma lem7178161 {A B C : Type'} (op : type1400 C) : term1 A B C op.
Proof. exact (@lem7178160 A B C op). Qed.
Lemma lem7178162 {A B C : Type'} (op : type1400 C) : (term1 A B C op) = (term2 A B C op).
Proof. exact (eq_refl (term1 A B C op)). Qed.
Lemma lem7178189 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7178190 {A : Type'} : (@sum A) = (@iterate real A real_add).
Proof. exact (@lem7178189 A). Qed.
Lemma lem7178191 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7178192 {A : Type'} (s : A -> Prop) : (@sum A s) = (@iterate real A real_add s).
Proof. exact (MK_COMB (@lem7178190 A) (@lem7178191 A s)). Qed.
Lemma lem7178194 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7178195 {B : Type'} : (@sum B) = (@iterate real B real_add).
Proof. exact (@lem7178194 B). Qed.
Lemma lem7178196 {A B : Type'} (t : type1413 A B) (i : A) : (t i) = (t i).
Proof. exact (eq_refl (t i)). Qed.
Lemma lem7178197 {A B : Type'} (t : type1413 A B) (i : A) : (term6 A B t i) = (term7 A B t i).
Proof. exact (MK_COMB (@lem7178195 B) (@lem7178196 A B t i)). Qed.
Lemma lem7178198 {A B : Type'} (x : type1416 A B) (i : A) : (x i) = (x i).
Proof. exact (eq_refl (x i)). Qed.
Lemma lem7178199 {A B : Type'} (t : type1413 A B) (x : type1416 A B) (i : A) : (term8 A B t x i) = (term9 A B t x i).
Proof. exact (MK_COMB (@lem7178197 A B t i) (@lem7178198 A B x i)). Qed.
Lemma lem7178200 {A B : Type'} (t : type1413 A B) (x : type1416 A B) : (term10 A B t x) = (term11 A B t x).
Proof. exact (fun_ext (fun i : A => @lem7178199 A B t x i)). Qed.
Lemma lem7178201 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : type1416 A B) : (term12 A B s t x) = (term13 A B s t x).
Proof. exact (MK_COMB (@lem7178192 A s) (@lem7178200 A B t x)). Qed.
Lemma lem7178202 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7178203 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : type1416 A B) : (term14 A B s t x) = (term15 A B s t x).
Proof. exact (MK_COMB (@lem7178202) (@lem7178201 A B s t x)). Qed.
Lemma lem7178205 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7178206 {A B : Type'} : (@sum (prod A B)) = (@iterate real (prod A B) real_add).
Proof. exact (@lem7178205 (prod A B)). Qed.
Lemma lem7178217 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term16 A B s t) = (term16 A B s t).
Proof. exact (eq_refl (term16 A B s t)). Qed.
Lemma lem7178218 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term17 A B s t) = (term18 A B s t).
Proof. exact (MK_COMB (@lem7178206 A B) (@lem7178217 A B s t)). Qed.
Lemma lem7178227 {A B : Type'} (x : type1416 A B) : (term19 A B x) = (term19 A B x).
Proof. exact (eq_refl (term19 A B x)). Qed.
Lemma lem7178228 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : type1416 A B) : (term20 A B s t x) = (term21 A B s t x).
Proof. exact (MK_COMB (@lem7178218 A B s t) (@lem7178227 A B x)). Qed.
Lemma lem7178229 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : type1416 A B) : ((term12 A B s t x) = (term20 A B s t x)) = ((term13 A B s t x) = (term21 A B s t x)).
Proof. exact (MK_COMB (@lem7178203 A B s t x) (@lem7178228 A B s t x)). Qed.
Lemma lem7178232 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term22 A B s t) = (term22 A B s t).
Proof. exact (eq_refl (term22 A B s t)). Qed.
Lemma lem7178233 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : type1416 A B) : (term23 A B s t x) = (term24 A B s t x).
Proof. exact (MK_COMB (@lem7178232 A B s t) (@lem7178229 A B s t x)). Qed.
Lemma lem7178236 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term25 A B s t) = (term26 A B s t).
Proof. exact (fun_ext (fun x : type1416 A B => @lem7178233 A B s t x)). Qed.
Lemma lem7178237 {A B : Type'} : (@all (A -> B -> real)) = (@all (A -> B -> real)).
Proof. exact (eq_refl (@all (A -> B -> real))). Qed.
Lemma lem7178238 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term27 A B s t) = (term28 A B s t).
Proof. exact (MK_COMB (@lem7178237 A B) (@lem7178236 A B s t)). Qed.
Lemma lem7178243 {A B : Type'} (s : A -> Prop) : (term29 A B s) = (term30 A B s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem7178238 A B s t)). Qed.
Lemma lem7178244 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem7178245 {A B : Type'} (s : A -> Prop) : (term31 A B s) = (term32 A B s).
Proof. exact (MK_COMB (@lem7178244 A B) (@lem7178243 A B s)). Qed.
Lemma lem7178250 {A B : Type'} : (term33 A B) = (term34 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7178245 A B s)). Qed.
Lemma lem7178251 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7178252 {A B : Type'} : (term35 A B) = (term36 A B).
Proof. exact (MK_COMB (@lem7178251 A) (@lem7178250 A B)). Qed.
Lemma lem7178257 {A B : Type'} : (term36 A B) = (term35 A B).
Proof. exact (SYM (@lem7178252 A B)). Qed.
Lemma lem7178259 {A B C : Type'} (op : type1400 C) : term2 A B C op.
Proof. exact (EQ_MP (@lem7178162 A B C op) (@lem7178161 A B C op)). Qed.
Lemma lem7178260 {A B : Type'} (op : type1627) : term37 A B op.
Proof. exact (@lem7178259 A B real op). Qed.
Lemma lem7178261 {A B : Type'} : term38 A B.
Proof. exact (@lem7178260 A B real_add). Qed.
Lemma lem7178263 : (@monoidal real real_add) = True.
Proof. exact (EQ_MP (@lem7178146) (@lem7067132)). Qed.
Lemma lem7178264 : True = (@monoidal real real_add).
Proof. exact (SYM (@lem7178263)). Qed.
Lemma lem7178265 : @monoidal real real_add.
Proof. exact (EQ_MP (@lem7178264) (@lem0)). Qed.
Lemma lem7178266 {A B : Type'} : term36 A B.
Proof. exact (@lem7178261 A B (@lem7178265)). Qed.
Lemma lem7178267 {A B : Type'} : term35 A B.
Proof. exact (EQ_MP (@lem7178257 A B) (@lem7178266 A B)). Qed.
