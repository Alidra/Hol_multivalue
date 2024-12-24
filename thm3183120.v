Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3183120_term_abbrevs.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm3183074_spec.
Require Import thm3183075_spec.
Require Import thm3183080_spec.
Require Import thm3183081_spec.
Lemma lem3183086 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3183081 A P x) (@lem3183080 A P x)). Qed.
Lemma lem3183087 {_83064 : Type'} (P : _83064 -> Prop) (x : _83064) : (@IN _83064 x P) = (P x).
Proof. exact (@lem3183086 _83064 P x). Qed.
Lemma lem3183088 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term0 _83064 x P) = (term1 _83064 P x).
Proof. exact (@lem3183087 _83064 (term2 _83064 P) x). Qed.
Lemma lem3183090 {A : Type'} (p : A -> Prop) : (@GSPEC A p) = p.
Proof. exact (EQ_MP (@lem3183075 A p) (@lem3183074 A p)). Qed.
Lemma lem3183091 {_83064 : Type'} (p : _83064 -> Prop) : (@GSPEC _83064 p) = p.
Proof. exact (@lem3183090 _83064 p). Qed.
Lemma lem3183092 {_83064 : Type'} (P : type919 _83064) : (term2 _83064 P) = (term3 _83064 P).
Proof. exact (@lem3183091 _83064 (term3 _83064 P)). Qed.
Lemma lem3183093 {_83064 : Type'} (x : _83064) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3183094 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term1 _83064 P x) = (term4 _83064 P x).
Proof. exact (MK_COMB (@lem3183092 _83064 P) (@lem3183093 _83064 x)). Qed.
Lemma lem3183096 {A B : Type'} (f : A -> B) (y : A) : (term5 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3183097 {_83064 : Type'} (f : _83064 -> Prop) (y : _83064) : (term6 _83064 f y) = (f y).
Proof. exact (@lem3183096 _83064 Prop f y). Qed.
Lemma lem3183098 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term7 _83064 P x) = (term4 _83064 P x).
Proof. exact (@lem3183097 _83064 (term3 _83064 P) x). Qed.
Lemma lem3183099 {_83064 : Type'} (P : type919 _83064) (v : _83064) : (term4 _83064 P v) = (term8 _83064 P v).
Proof. exact (eq_refl (term4 _83064 P v)). Qed.
Lemma lem3183100 {_83064 : Type'} (P : type919 _83064) : (term9 _83064 P) = (term3 _83064 P).
Proof. exact (fun_ext (fun v : _83064 => @lem3183099 _83064 P v)). Qed.
Lemma lem3183101 {_83064 : Type'} (x : _83064) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3183102 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term7 _83064 P x) = (term4 _83064 P x).
Proof. exact (MK_COMB (@lem3183100 _83064 P) (@lem3183101 _83064 x)). Qed.
Lemma lem3183103 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3183104 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term10 _83064 P x) = (term11 _83064 P x).
Proof. exact (MK_COMB (@lem3183103) (@lem3183102 _83064 P x)). Qed.
Lemma lem3183105 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term4 _83064 P x) = (term8 _83064 P x).
Proof. exact (eq_refl (term4 _83064 P x)). Qed.
Lemma lem3183106 {_83064 : Type'} (P : type919 _83064) (x : _83064) : ((term7 _83064 P x) = (term4 _83064 P x)) = ((term4 _83064 P x) = (term8 _83064 P x)).
Proof. exact (MK_COMB (@lem3183104 _83064 P x) (@lem3183105 _83064 P x)). Qed.
Lemma lem3183107 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term4 _83064 P x) = (term8 _83064 P x).
Proof. exact (EQ_MP (@lem3183106 _83064 P x) (@lem3183098 _83064 P x)). Qed.
Lemma lem3183108 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term1 _83064 P x) = (term8 _83064 P x).
Proof. exact (TRANS (@lem3183094 _83064 P x) (@lem3183107 _83064 P x)). Qed.
Lemma lem3183109 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term0 _83064 x P) = (term8 _83064 P x).
Proof. exact (TRANS (@lem3183088 _83064 P x) (@lem3183108 _83064 P x)). Qed.
Lemma lem3183110 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3183111 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term12 _83064 x P) = (term13 _83064 P x).
Proof. exact (MK_COMB (@lem3183110) (@lem3183109 _83064 P x)). Qed.
Lemma lem3183116 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term14 _83064 P x) = (term14 _83064 P x).
Proof. exact (eq_refl (term14 _83064 P x)). Qed.
Lemma lem3183117 {_83064 : Type'} (P : type919 _83064) (x : _83064) : ((term0 _83064 x P) = (term14 _83064 P x)) = ((term8 _83064 P x) = (term14 _83064 P x)).
Proof. exact (MK_COMB (@lem3183111 _83064 P x) (@lem3183116 _83064 P x)). Qed.
Lemma lem3183120 {_83064 : Type'} (P : type919 _83064) (x : _83064) : ((term8 _83064 P x) = (term14 _83064 P x)) = ((term0 _83064 x P) = (term14 _83064 P x)).
Proof. exact (SYM (@lem3183117 _83064 P x)). Qed.
