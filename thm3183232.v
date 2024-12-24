Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3183232_term_abbrevs.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm3183074_spec.
Require Import thm3183075_spec.
Lemma lem3183199 {A : Type'} (p : A -> Prop) : (@GSPEC A p) = p.
Proof. exact (EQ_MP (@lem3183075 A p) (@lem3183074 A p)). Qed.
Lemma lem3183200 {_83152 : Type'} (p : _83152 -> Prop) : (@GSPEC _83152 p) = p.
Proof. exact (@lem3183199 _83152 p). Qed.
Lemma lem3183201 {_83152 : Type'} (p : _83152 -> Prop) : (term0 _83152 p) = (term1 _83152 p).
Proof. exact (@lem3183200 _83152 (term1 _83152 p)). Qed.
Lemma lem3183206 {_83152 : Type'} (x : _83152) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3183207 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term2 _83152 p x) = (term3 _83152 p x).
Proof. exact (MK_COMB (@lem3183201 _83152 p) (@lem3183206 _83152 x)). Qed.
Lemma lem3183209 {A B : Type'} (f : A -> B) (y : A) : (term4 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3183210 {_83152 : Type'} (f : _83152 -> Prop) (y : _83152) : (term5 _83152 f y) = (f y).
Proof. exact (@lem3183209 _83152 Prop f y). Qed.
Lemma lem3183211 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term6 _83152 p x) = (term3 _83152 p x).
Proof. exact (@lem3183210 _83152 (term1 _83152 p) x). Qed.
Lemma lem3183212 {_83152 : Type'} (v : _83152) (p : _83152 -> Prop) : (term3 _83152 p v) = (term7 _83152 v p).
Proof. exact (eq_refl (term3 _83152 p v)). Qed.
Lemma lem3183213 {_83152 : Type'} (p : _83152 -> Prop) : (term8 _83152 p) = (term1 _83152 p).
Proof. exact (fun_ext (fun v : _83152 => @lem3183212 _83152 v p)). Qed.
Lemma lem3183214 {_83152 : Type'} (x : _83152) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3183215 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term6 _83152 p x) = (term3 _83152 p x).
Proof. exact (MK_COMB (@lem3183213 _83152 p) (@lem3183214 _83152 x)). Qed.
Lemma lem3183216 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3183217 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term9 _83152 p x) = (term10 _83152 p x).
Proof. exact (MK_COMB (@lem3183216) (@lem3183215 _83152 p x)). Qed.
Lemma lem3183218 {_83152 : Type'} (x : _83152) (p : _83152 -> Prop) : (term3 _83152 p x) = (term7 _83152 x p).
Proof. exact (eq_refl (term3 _83152 p x)). Qed.
Lemma lem3183219 {_83152 : Type'} (x : _83152) (p : _83152 -> Prop) : ((term6 _83152 p x) = (term3 _83152 p x)) = ((term3 _83152 p x) = (term7 _83152 x p)).
Proof. exact (MK_COMB (@lem3183217 _83152 p x) (@lem3183218 _83152 x p)). Qed.
Lemma lem3183220 {_83152 : Type'} (x : _83152) (p : _83152 -> Prop) : (term3 _83152 p x) = (term7 _83152 x p).
Proof. exact (EQ_MP (@lem3183219 _83152 x p) (@lem3183211 _83152 p x)). Qed.
Lemma lem3183225 {_83152 : Type'} (x : _83152) (p : _83152 -> Prop) : (term2 _83152 p x) = (term7 _83152 x p).
Proof. exact (TRANS (@lem3183207 _83152 p x) (@lem3183220 _83152 x p)). Qed.
Lemma lem3183226 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3183227 {_83152 : Type'} (x : _83152) (p : _83152 -> Prop) : (term11 _83152 p x) = (term12 _83152 x p).
Proof. exact (MK_COMB (@lem3183226) (@lem3183225 _83152 x p)). Qed.
Lemma lem3183228 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (p x) = (p x).
Proof. exact (eq_refl (p x)). Qed.
Lemma lem3183229 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : ((term2 _83152 p x) = (p x)) = ((term7 _83152 x p) = (p x)).
Proof. exact (MK_COMB (@lem3183227 _83152 x p) (@lem3183228 _83152 p x)). Qed.
Lemma lem3183232 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : ((term7 _83152 x p) = (p x)) = ((term2 _83152 p x) = (p x)).
Proof. exact (SYM (@lem3183229 _83152 p x)). Qed.
