Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3183195_term_abbrevs.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm3183074_spec.
Require Import thm3183075_spec.
Lemma lem3183166 {A : Type'} (p : A -> Prop) : (@GSPEC A p) = p.
Proof. exact (EQ_MP (@lem3183075 A p) (@lem3183074 A p)). Qed.
Lemma lem3183167 {_83123 : Type'} (p : _83123 -> Prop) : (@GSPEC _83123 p) = p.
Proof. exact (@lem3183166 _83123 p). Qed.
Lemma lem3183168 {_83123 : Type'} (P : type919 _83123) : (term0 _83123 P) = (term1 _83123 P).
Proof. exact (@lem3183167 _83123 (term1 _83123 P)). Qed.
Lemma lem3183169 {_83123 : Type'} (x : _83123) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3183170 {_83123 : Type'} (P : type919 _83123) (x : _83123) : (term2 _83123 P x) = (term3 _83123 P x).
Proof. exact (MK_COMB (@lem3183168 _83123 P) (@lem3183169 _83123 x)). Qed.
Lemma lem3183172 {A B : Type'} (f : A -> B) (y : A) : (term4 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3183173 {_83123 : Type'} (f : _83123 -> Prop) (y : _83123) : (term5 _83123 f y) = (f y).
Proof. exact (@lem3183172 _83123 Prop f y). Qed.
Lemma lem3183174 {_83123 : Type'} (P : type919 _83123) (x : _83123) : (term6 _83123 P x) = (term3 _83123 P x).
Proof. exact (@lem3183173 _83123 (term1 _83123 P) x). Qed.
Lemma lem3183175 {_83123 : Type'} (P : type919 _83123) (v : _83123) : (term3 _83123 P v) = (term7 _83123 P v).
Proof. exact (eq_refl (term3 _83123 P v)). Qed.
Lemma lem3183176 {_83123 : Type'} (P : type919 _83123) : (term8 _83123 P) = (term1 _83123 P).
Proof. exact (fun_ext (fun v : _83123 => @lem3183175 _83123 P v)). Qed.
Lemma lem3183177 {_83123 : Type'} (x : _83123) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3183178 {_83123 : Type'} (P : type919 _83123) (x : _83123) : (term6 _83123 P x) = (term3 _83123 P x).
Proof. exact (MK_COMB (@lem3183176 _83123 P) (@lem3183177 _83123 x)). Qed.
Lemma lem3183179 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3183180 {_83123 : Type'} (P : type919 _83123) (x : _83123) : (term9 _83123 P x) = (term10 _83123 P x).
Proof. exact (MK_COMB (@lem3183179) (@lem3183178 _83123 P x)). Qed.
Lemma lem3183181 {_83123 : Type'} (P : type919 _83123) (x : _83123) : (term3 _83123 P x) = (term7 _83123 P x).
Proof. exact (eq_refl (term3 _83123 P x)). Qed.
Lemma lem3183182 {_83123 : Type'} (P : type919 _83123) (x : _83123) : ((term6 _83123 P x) = (term3 _83123 P x)) = ((term3 _83123 P x) = (term7 _83123 P x)).
Proof. exact (MK_COMB (@lem3183180 _83123 P x) (@lem3183181 _83123 P x)). Qed.
Lemma lem3183183 {_83123 : Type'} (P : type919 _83123) (x : _83123) : (term3 _83123 P x) = (term7 _83123 P x).
Proof. exact (EQ_MP (@lem3183182 _83123 P x) (@lem3183174 _83123 P x)). Qed.
Lemma lem3183184 {_83123 : Type'} (P : type919 _83123) (x : _83123) : (term2 _83123 P x) = (term7 _83123 P x).
Proof. exact (TRANS (@lem3183170 _83123 P x) (@lem3183183 _83123 P x)). Qed.
Lemma lem3183185 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3183186 {_83123 : Type'} (P : type919 _83123) (x : _83123) : (term11 _83123 P x) = (term12 _83123 P x).
Proof. exact (MK_COMB (@lem3183185) (@lem3183184 _83123 P x)). Qed.
Lemma lem3183191 {_83123 : Type'} (P : type919 _83123) (x : _83123) : (term13 _83123 P x) = (term13 _83123 P x).
Proof. exact (eq_refl (term13 _83123 P x)). Qed.
Lemma lem3183192 {_83123 : Type'} (P : type919 _83123) (x : _83123) : ((term2 _83123 P x) = (term13 _83123 P x)) = ((term7 _83123 P x) = (term13 _83123 P x)).
Proof. exact (MK_COMB (@lem3183186 _83123 P x) (@lem3183191 _83123 P x)). Qed.
Lemma lem3183195 {_83123 : Type'} (P : type919 _83123) (x : _83123) : ((term7 _83123 P x) = (term13 _83123 P x)) = ((term2 _83123 P x) = (term13 _83123 P x)).
Proof. exact (SYM (@lem3183192 _83123 P x)). Qed.
