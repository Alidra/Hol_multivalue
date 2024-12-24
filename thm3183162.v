Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3183162_term_abbrevs.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm3183074_spec.
Require Import thm3183075_spec.
Require Import thm3183080_spec.
Require Import thm3183081_spec.
Lemma lem3183124 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3183081 A P x) (@lem3183080 A P x)). Qed.
Lemma lem3183125 {_83095 : Type'} (P : _83095 -> Prop) (x : _83095) : (@IN _83095 x P) = (P x).
Proof. exact (@lem3183124 _83095 P x). Qed.
Lemma lem3183126 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term0 _83095 x p) = (term1 _83095 p x).
Proof. exact (@lem3183125 _83095 (term2 _83095 p) x). Qed.
Lemma lem3183128 {A : Type'} (p : A -> Prop) : (@GSPEC A p) = p.
Proof. exact (EQ_MP (@lem3183075 A p) (@lem3183074 A p)). Qed.
Lemma lem3183129 {_83095 : Type'} (p : _83095 -> Prop) : (@GSPEC _83095 p) = p.
Proof. exact (@lem3183128 _83095 p). Qed.
Lemma lem3183130 {_83095 : Type'} (p : _83095 -> Prop) : (term2 _83095 p) = (term3 _83095 p).
Proof. exact (@lem3183129 _83095 (term3 _83095 p)). Qed.
Lemma lem3183135 {_83095 : Type'} (x : _83095) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3183136 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term1 _83095 p x) = (term4 _83095 p x).
Proof. exact (MK_COMB (@lem3183130 _83095 p) (@lem3183135 _83095 x)). Qed.
Lemma lem3183138 {A B : Type'} (f : A -> B) (y : A) : (term5 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3183139 {_83095 : Type'} (f : _83095 -> Prop) (y : _83095) : (term6 _83095 f y) = (f y).
Proof. exact (@lem3183138 _83095 Prop f y). Qed.
Lemma lem3183140 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term7 _83095 p x) = (term4 _83095 p x).
Proof. exact (@lem3183139 _83095 (term3 _83095 p) x). Qed.
Lemma lem3183141 {_83095 : Type'} (v : _83095) (p : _83095 -> Prop) : (term4 _83095 p v) = (term8 _83095 v p).
Proof. exact (eq_refl (term4 _83095 p v)). Qed.
Lemma lem3183142 {_83095 : Type'} (p : _83095 -> Prop) : (term9 _83095 p) = (term3 _83095 p).
Proof. exact (fun_ext (fun v : _83095 => @lem3183141 _83095 v p)). Qed.
Lemma lem3183143 {_83095 : Type'} (x : _83095) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3183144 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term7 _83095 p x) = (term4 _83095 p x).
Proof. exact (MK_COMB (@lem3183142 _83095 p) (@lem3183143 _83095 x)). Qed.
Lemma lem3183145 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3183146 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term10 _83095 p x) = (term11 _83095 p x).
Proof. exact (MK_COMB (@lem3183145) (@lem3183144 _83095 p x)). Qed.
Lemma lem3183147 {_83095 : Type'} (x : _83095) (p : _83095 -> Prop) : (term4 _83095 p x) = (term8 _83095 x p).
Proof. exact (eq_refl (term4 _83095 p x)). Qed.
Lemma lem3183148 {_83095 : Type'} (x : _83095) (p : _83095 -> Prop) : ((term7 _83095 p x) = (term4 _83095 p x)) = ((term4 _83095 p x) = (term8 _83095 x p)).
Proof. exact (MK_COMB (@lem3183146 _83095 p x) (@lem3183147 _83095 x p)). Qed.
Lemma lem3183149 {_83095 : Type'} (x : _83095) (p : _83095 -> Prop) : (term4 _83095 p x) = (term8 _83095 x p).
Proof. exact (EQ_MP (@lem3183148 _83095 x p) (@lem3183140 _83095 p x)). Qed.
Lemma lem3183154 {_83095 : Type'} (x : _83095) (p : _83095 -> Prop) : (term1 _83095 p x) = (term8 _83095 x p).
Proof. exact (TRANS (@lem3183136 _83095 p x) (@lem3183149 _83095 x p)). Qed.
Lemma lem3183155 {_83095 : Type'} (x : _83095) (p : _83095 -> Prop) : (term0 _83095 x p) = (term8 _83095 x p).
Proof. exact (TRANS (@lem3183126 _83095 p x) (@lem3183154 _83095 x p)). Qed.
Lemma lem3183156 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3183157 {_83095 : Type'} (x : _83095) (p : _83095 -> Prop) : (term12 _83095 x p) = (term13 _83095 x p).
Proof. exact (MK_COMB (@lem3183156) (@lem3183155 _83095 x p)). Qed.
Lemma lem3183158 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (p x) = (p x).
Proof. exact (eq_refl (p x)). Qed.
Lemma lem3183159 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : ((term0 _83095 x p) = (p x)) = ((term8 _83095 x p) = (p x)).
Proof. exact (MK_COMB (@lem3183157 _83095 x p) (@lem3183158 _83095 p x)). Qed.
Lemma lem3183162 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : ((term8 _83095 x p) = (p x)) = ((term0 _83095 x p) = (p x)).
Proof. exact (SYM (@lem3183159 _83095 p x)). Qed.
