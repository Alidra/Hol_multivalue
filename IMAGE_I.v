Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMAGE_I_term_abbrevs.
Require Import IMAGE_ID_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem3368912 {_87528 : Type'} (s : _87528 -> Prop) : term0 _87528 s.
Proof. exact (@lem3368911 _87528 s). Qed.
Lemma lem3368913 {_87528 : Type'} (s : _87528 -> Prop) : (term0 _87528 s) = ((term1 _87528 s) = s).
Proof. exact (eq_refl (term0 _87528 s)). Qed.
Lemma lem3368922 {A : Type'} : (@I A) = (term2 A).
Proof. exact (@I_def A). Qed.
Lemma lem3368923 {_87542 : Type'} : (@I _87542) = (term2 _87542).
Proof. exact (@lem3368922 _87542). Qed.
Lemma lem3368924 {_87542 : Type'} : (@IMAGE _87542 _87542) = (@IMAGE _87542 _87542).
Proof. exact (eq_refl (@IMAGE _87542 _87542)). Qed.
Lemma lem3368925 {_87542 : Type'} : (@IMAGE _87542 _87542 (@I _87542)) = (term3 _87542).
Proof. exact (MK_COMB (@lem3368924 _87542) (@lem3368923 _87542)). Qed.
Lemma lem3368926 {_87542 : Type'} (s : _87542 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3368927 {_87542 : Type'} (s : _87542 -> Prop) : (@IMAGE _87542 _87542 (@I _87542) s) = (term1 _87542 s).
Proof. exact (MK_COMB (@lem3368925 _87542) (@lem3368926 _87542 s)). Qed.
Lemma lem3368929 {_87528 : Type'} (s : _87528 -> Prop) : (term1 _87528 s) = s.
Proof. exact (EQ_MP (@lem3368913 _87528 s) (@lem3368912 _87528 s)). Qed.
Lemma lem3368930 {_87542 : Type'} (s : _87542 -> Prop) : (term1 _87542 s) = s.
Proof. exact (@lem3368929 _87542 s). Qed.
Lemma lem3368931 {_87542 : Type'} (s : _87542 -> Prop) : (@IMAGE _87542 _87542 (@I _87542) s) = s.
Proof. exact (TRANS (@lem3368927 _87542 s) (@lem3368930 _87542 s)). Qed.
Lemma lem3368932 {_87542 : Type'} : (@eq (_87542 -> Prop)) = (@eq (_87542 -> Prop)).
Proof. exact (eq_refl (@eq (_87542 -> Prop))). Qed.
Lemma lem3368933 {_87542 : Type'} (s : _87542 -> Prop) : (term4 _87542 s) = (@eq (_87542 -> Prop) s).
Proof. exact (MK_COMB (@lem3368932 _87542) (@lem3368931 _87542 s)). Qed.
Lemma lem3368934 {_87542 : Type'} (s : _87542 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3368935 {_87542 : Type'} (s : _87542 -> Prop) : ((@IMAGE _87542 _87542 (@I _87542) s) = s) = (s = s).
Proof. exact (MK_COMB (@lem3368933 _87542 s) (@lem3368934 _87542 s)). Qed.
Lemma lem3368937 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3368938 {_87542 : Type'} (x : _87542 -> Prop) : (x = x) = True.
Proof. exact (@lem3368937 (_87542 -> Prop) x). Qed.
Lemma lem3368939 {_87542 : Type'} (s : _87542 -> Prop) : (s = s) = True.
Proof. exact (@lem3368938 _87542 s). Qed.
Lemma lem3368940 {_87542 : Type'} (s : _87542 -> Prop) : ((@IMAGE _87542 _87542 (@I _87542) s) = s) = True.
Proof. exact (TRANS (@lem3368935 _87542 s) (@lem3368939 _87542 s)). Qed.
Lemma lem3368941 {_87542 : Type'} : (term5 _87542) = (term6 _87542).
Proof. exact (fun_ext (fun s : _87542 -> Prop => @lem3368940 _87542 s)). Qed.
Lemma lem3368942 {_87542 : Type'} : (@all (_87542 -> Prop)) = (@all (_87542 -> Prop)).
Proof. exact (eq_refl (@all (_87542 -> Prop))). Qed.
Lemma lem3368943 {_87542 : Type'} : (term7 _87542) = (term8 _87542).
Proof. exact (MK_COMB (@lem3368942 _87542) (@lem3368941 _87542)). Qed.
Lemma lem3368945 {A : Type'} (t : Prop) : (term9 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3368946 {_87542 : Type'} (t : Prop) : (term10 _87542 t) = t.
Proof. exact (@lem3368945 (_87542 -> Prop) t). Qed.
Lemma lem3368947 {_87542 : Type'} : (term8 _87542) = True.
Proof. exact (@lem3368946 _87542 True). Qed.
Lemma lem3368948 {_87542 : Type'} : (term7 _87542) = True.
Proof. exact (TRANS (@lem3368943 _87542) (@lem3368947 _87542)). Qed.
Lemma lem3368949 {_87542 : Type'} : True = (term7 _87542).
Proof. exact (SYM (@lem3368948 _87542)). Qed.
Lemma lem3368950 {_87542 : Type'} : term7 _87542.
Proof. exact (EQ_MP (@lem3368949 _87542) (@lem0)). Qed.
