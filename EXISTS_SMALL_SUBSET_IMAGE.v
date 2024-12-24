Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_SMALL_SUBSET_IMAGE_term_abbrevs.
Require Import CARD_IMAGE_LE_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EXISTS_SMALL_SUBSET_IMAGE_INJ_spec.
Require Import FINITE_IMAGE_spec.
Require Import IMAGE_SUBSET_spec.
Require Import LET_TRANS_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18394_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm32_spec.
Require Import thm69_spec.
Lemma lem4067920 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4067921 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4067922 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4067921 t1) (@lem4067920 t1)). Qed.
Lemma lem4067923 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4067922 t1 t2). Qed.
Lemma lem4067924 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4067925 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4067924 t1 t2) (@lem4067923 t1 t2)). Qed.
Lemma lem4067926 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4067925 t1 t2 t3). Qed.
Lemma lem4067927 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4067928 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4067927 t1 t2 t3) (@lem4067926 t1 t2 t3)). Qed.
Lemma lem4067929 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4067928 t1 t2 t3)). Qed.
Lemma lem4067940 {_102126 _102133 : Type'} (P : type686 _102133) : term7 _102126 _102133 P.
Proof. exact (@lem4067239 _102126 _102133 P). Qed.
Lemma lem4067941 {_102126 _102133 : Type'} (P : type686 _102133) : (term7 _102126 _102133 P) = (term8 _102126 _102133 P).
Proof. exact (eq_refl (term7 _102126 _102133 P)). Qed.
Lemma lem4067942 {_102126 _102133 : Type'} (P : type686 _102133) : term8 _102126 _102133 P.
Proof. exact (EQ_MP (@lem4067941 _102126 _102133 P) (@lem4067940 _102126 _102133 P)). Qed.
Lemma lem4067943 {_102126 _102133 : Type'} (P : type686 _102133) (f : _102126 -> _102133) : term9 _102126 _102133 P f.
Proof. exact (@lem4067942 _102126 _102133 P f). Qed.
Lemma lem4067944 {_102126 _102133 : Type'} (P : type686 _102133) (f : _102126 -> _102133) : (term9 _102126 _102133 P f) = (term10 _102126 _102133 P f).
Proof. exact (eq_refl (term9 _102126 _102133 P f)). Qed.
Lemma lem4067945 {_102126 _102133 : Type'} (P : type686 _102133) (f : _102126 -> _102133) : term10 _102126 _102133 P f.
Proof. exact (EQ_MP (@lem4067944 _102126 _102133 P f) (@lem4067943 _102126 _102133 P f)). Qed.
Lemma lem4067946 {_102126 _102133 : Type'} (P : type686 _102133) (f : _102126 -> _102133) (s : _102126 -> Prop) : term11 _102126 _102133 P f s.
Proof. exact (@lem4067945 _102126 _102133 P f s). Qed.
Lemma lem4067947 {_102126 _102133 : Type'} (s : _102126 -> Prop) (P : type686 _102133) (f : _102126 -> _102133) : (term11 _102126 _102133 P f s) = (term12 _102126 _102133 s P f).
Proof. exact (eq_refl (term11 _102126 _102133 P f s)). Qed.
Lemma lem4067948 {_102126 _102133 : Type'} (s : _102126 -> Prop) (P : type686 _102133) (f : _102126 -> _102133) : term12 _102126 _102133 s P f.
Proof. exact (EQ_MP (@lem4067947 _102126 _102133 s P f) (@lem4067946 _102126 _102133 P f s)). Qed.
Lemma lem4067949 {_102126 _102133 : Type'} (s : _102126 -> Prop) (P : type686 _102133) (f : _102126 -> _102133) (n : nat) : term13 _102126 _102133 s P f n.
Proof. exact (@lem4067948 _102126 _102133 s P f n). Qed.
Lemma lem4067950 {_102126 _102133 : Type'} (n : nat) (s : _102126 -> Prop) (P : type686 _102133) (f : _102126 -> _102133) : (term13 _102126 _102133 s P f n) = ((term14 _102126 _102133 n f s P) = (term15 _102126 _102133 n s P f)).
Proof. exact (eq_refl (term13 _102126 _102133 s P f n)). Qed.
Lemma lem4067955 {_102126 _102133 : Type'} (n : nat) (s : _102126 -> Prop) (P : type686 _102133) (f : _102126 -> _102133) : (term14 _102126 _102133 n f s P) = (term15 _102126 _102133 n s P f).
Proof. exact (EQ_MP (@lem4067950 _102126 _102133 n s P f) (@lem4067949 _102126 _102133 s P f n)). Qed.
Lemma lem4067956 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term14 _102289 _102316 n f s P) = (term15 _102289 _102316 n s P f).
Proof. exact (@lem4067955 _102289 _102316 n s P f). Qed.
Lemma lem4067987 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4067988 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term16 _102289 _102316 n f s P) = (term17 _102289 _102316 n s P f).
Proof. exact (MK_COMB (@lem4067987) (@lem4067956 _102289 _102316 n s P f)). Qed.
Lemma lem4067999 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term18 _102289 _102316 n s P f) = (term18 _102289 _102316 n s P f).
Proof. exact (eq_refl (term18 _102289 _102316 n s P f)). Qed.
Lemma lem4068000 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term19 _102289 _102316 n s P f) = (term20 _102289 _102316 n s P f).
Proof. exact (MK_COMB (@lem4067988 _102289 _102316 n s P f) (@lem4067999 _102289 _102316 n s P f)). Qed.
Lemma lem4068003 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term20 _102289 _102316 n s P f) = (term19 _102289 _102316 n s P f).
Proof. exact (SYM (@lem4068000 _102289 _102316 n s P f)). Qed.
Lemma lem4068005 (p : Prop) : p = (term21 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4068006 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term20 _102289 _102316 n s P f) = (term22 _102289 _102316 n s P f).
Proof. exact (@lem4068005 (term20 _102289 _102316 n s P f)). Qed.
Lemma lem4068007 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term22 _102289 _102316 n s P f) = (term20 _102289 _102316 n s P f).
Proof. exact (SYM (@lem4068006 _102289 _102316 n s P f)). Qed.
Lemma lem4068008 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (h1 : term23 _102289 _102316 n s P f) : term23 _102289 _102316 n s P f.
Proof. exact (h1). Qed.
Lemma lem4068011 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (h1 : term22 _102289 _102316 n s P f) : term22 _102289 _102316 n s P f.
Proof. exact (h1). Qed.
Lemma lem4068012 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : term24 _102289 _102316 n s P f.
Proof. exact (fun h0 : term22 _102289 _102316 n s P f => @lem4068011 _102289 _102316 n s P f h0). Qed.
Lemma lem4068013 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (h1 : term24 _102289 _102316 n s P f) : term24 _102289 _102316 n s P f.
Proof. exact (h1). Qed.
Lemma lem4068014 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (h1 : term22 _102289 _102316 n s P f) : term22 _102289 _102316 n s P f.
Proof. exact (h1). Qed.
Lemma lem4068015 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (h1 : term22 _102289 _102316 n s P f) (h2 : term24 _102289 _102316 n s P f) : term22 _102289 _102316 n s P f.
Proof. exact (@lem4068013 _102289 _102316 n s P f h2 (@lem4068014 _102289 _102316 n s P f h1)). Qed.
Lemma lem4068016 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (h1 : term22 _102289 _102316 n s P f) : term25 _102289 _102316 n s P f.
Proof. exact (fun h0 : term24 _102289 _102316 n s P f => @lem4068015 _102289 _102316 n s P f h1 h0). Qed.
Lemma lem4068017 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (h1 : term24 _102289 _102316 n s P f) : term24 _102289 _102316 n s P f.
Proof. exact (h1). Qed.
Lemma lem4068018 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (h1 : term22 _102289 _102316 n s P f) (h2 : term24 _102289 _102316 n s P f) : term22 _102289 _102316 n s P f.
Proof. exact (@lem4068016 _102289 _102316 n s P f h1 (@lem4068017 _102289 _102316 n s P f h2)). Qed.
Lemma lem4068019 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (h1 : term24 _102289 _102316 n s P f) : term24 _102289 _102316 n s P f.
Proof. exact (fun h0 : term22 _102289 _102316 n s P f => @lem4068018 _102289 _102316 n s P f h0 h1). Qed.
Lemma lem4068020 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : term26 _102289 _102316 n s P f.
Proof. exact (fun h0 : term24 _102289 _102316 n s P f => @lem4068019 _102289 _102316 n s P f h0). Qed.
Lemma lem4068023 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : term24 _102289 _102316 n s P f.
Proof. exact (@lem4068020 _102289 _102316 n s P f (@lem4068012 _102289 _102316 n s P f)). Qed.
Lemma lem4068024 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : term24 _102289 _102316 n s P f.
Proof. exact (@lem4068023 _102289 _102316 n s P f). Qed.
Lemma lem4068042 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4068043 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term22 _102289 _102316 n s P f) = (term27 _102289 _102316 n s P f).
Proof. exact (@lem4068042 (term23 _102289 _102316 n s P f)). Qed.
Lemma lem4068045 (t : Prop) : (term28 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4068046 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term27 _102289 _102316 n s P f) = (term20 _102289 _102316 n s P f).
Proof. exact (@lem4068045 (term20 _102289 _102316 n s P f)). Qed.
Lemma lem4068049 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term22 _102289 _102316 n s P f) = (term20 _102289 _102316 n s P f).
Proof. exact (TRANS (@lem4068043 _102289 _102316 n s P f) (@lem4068046 _102289 _102316 n s P f)). Qed.
Lemma lem4068132 {_102289 _102316 : Type'} (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term29 _102289 _102316 s P f) = (term30 _102289 _102316 s P f).
Proof. exact (fun_ext (fun n : nat => @lem4068049 _102289 _102316 n s P f)). Qed.
Lemma lem4068133 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4068134 {_102289 _102316 : Type'} (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term31 _102289 _102316 s P f) = (term32 _102289 _102316 s P f).
Proof. exact (MK_COMB (@lem4068133) (@lem4068132 _102289 _102316 s P f)). Qed.
Lemma lem4068139 {_102289 _102316 : Type'} (P : type686 _102316) (f : _102289 -> _102316) : (term33 _102289 _102316 P f) = (term34 _102289 _102316 P f).
Proof. exact (fun_ext (fun s : _102289 -> Prop => @lem4068134 _102289 _102316 s P f)). Qed.
Lemma lem4068140 {_102289 : Type'} : (@all (_102289 -> Prop)) = (@all (_102289 -> Prop)).
Proof. exact (eq_refl (@all (_102289 -> Prop))). Qed.
Lemma lem4068141 {_102289 _102316 : Type'} (P : type686 _102316) (f : _102289 -> _102316) : (term35 _102289 _102316 P f) = (term36 _102289 _102316 P f).
Proof. exact (MK_COMB (@lem4068140 _102289) (@lem4068139 _102289 _102316 P f)). Qed.
Lemma lem4068146 {_102289 _102316 : Type'} (f : _102289 -> _102316) : (term37 _102289 _102316 f) = (term38 _102289 _102316 f).
Proof. exact (fun_ext (fun P : type686 _102316 => @lem4068141 _102289 _102316 P f)). Qed.
Lemma lem4068147 {_102316 : Type'} : (@all ((_102316 -> Prop) -> Prop)) = (@all ((_102316 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_102316 -> Prop) -> Prop))). Qed.
Lemma lem4068148 {_102289 _102316 : Type'} (f : _102289 -> _102316) : (term39 _102289 _102316 f) = (term40 _102289 _102316 f).
Proof. exact (MK_COMB (@lem4068147 _102316) (@lem4068146 _102289 _102316 f)). Qed.
Lemma lem4068153 {_102289 _102316 : Type'} : (term41 _102289 _102316) = (term42 _102289 _102316).
Proof. exact (fun_ext (fun f : _102289 -> _102316 => @lem4068148 _102289 _102316 f)). Qed.
Lemma lem4068154 {_102289 _102316 : Type'} : (@all (_102289 -> _102316)) = (@all (_102289 -> _102316)).
Proof. exact (eq_refl (@all (_102289 -> _102316))). Qed.
Lemma lem4068163 {_102289 _102316 : Type'} : (term43 _102289 _102316) = (term44 _102289 _102316).
Proof. exact (MK_COMB (@lem4068154 _102289 _102316) (@lem4068153 _102289 _102316)). Qed.
Lemma lem4068176 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term45 _102289 _102316 n s P f t) = (term45 _102289 _102316 n s P f t).
Proof. exact (eq_refl (term45 _102289 _102316 n s P f t)). Qed.
Lemma lem4068177 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term46 _102289 _102316 n s P f) = (term46 _102289 _102316 n s P f).
Proof. exact (fun_ext (fun t : _102289 -> Prop => @lem4068176 _102289 _102316 n s P f t)). Qed.
Lemma lem4068178 {_102289 : Type'} : (@ex (_102289 -> Prop)) = (@ex (_102289 -> Prop)).
Proof. exact (eq_refl (@ex (_102289 -> Prop))). Qed.
Lemma lem4068179 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term18 _102289 _102316 n s P f) = (term18 _102289 _102316 n s P f).
Proof. exact (MK_COMB (@lem4068178 _102289) (@lem4068177 _102289 _102316 n s P f)). Qed.
Lemma lem4068180 {_102289 _102316 : Type'} (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term47 _102289 _102316 P f t) = (term47 _102289 _102316 P f t).
Proof. exact (eq_refl (term47 _102289 _102316 P f t)). Qed.
Lemma lem4068193 {_102289 _102316 : Type'} (t : _102289 -> Prop) (f : _102289 -> _102316) (x : _102289) (y : _102289) : (term48 _102289 _102316 t f x y) = (term48 _102289 _102316 t f x y).
Proof. exact (eq_refl (term48 _102289 _102316 t f x y)). Qed.
Lemma lem4068194 {_102289 _102316 : Type'} (t : _102289 -> Prop) (f : _102289 -> _102316) (x : _102289) : (term49 _102289 _102316 t f x) = (term49 _102289 _102316 t f x).
Proof. exact (fun_ext (fun y : _102289 => @lem4068193 _102289 _102316 t f x y)). Qed.
Lemma lem4068195 {_102289 : Type'} : (@all _102289) = (@all _102289).
Proof. exact (eq_refl (@all _102289)). Qed.
Lemma lem4068196 {_102289 _102316 : Type'} (t : _102289 -> Prop) (f : _102289 -> _102316) (x : _102289) : (term50 _102289 _102316 t f x) = (term50 _102289 _102316 t f x).
Proof. exact (MK_COMB (@lem4068195 _102289) (@lem4068194 _102289 _102316 t f x)). Qed.
Lemma lem4068197 {_102289 _102316 : Type'} (t : _102289 -> Prop) (f : _102289 -> _102316) : (term51 _102289 _102316 t f) = (term51 _102289 _102316 t f).
Proof. exact (fun_ext (fun x : _102289 => @lem4068196 _102289 _102316 t f x)). Qed.
Lemma lem4068198 {_102289 : Type'} : (@all _102289) = (@all _102289).
Proof. exact (eq_refl (@all _102289)). Qed.
Lemma lem4068199 {_102289 _102316 : Type'} (t : _102289 -> Prop) (f : _102289 -> _102316) : (term52 _102289 _102316 t f) = (term52 _102289 _102316 t f).
Proof. exact (MK_COMB (@lem4068198 _102289) (@lem4068197 _102289 _102316 t f)). Qed.
Lemma lem4068200 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4068201 {_102289 _102316 : Type'} (t : _102289 -> Prop) (f : _102289 -> _102316) : (term53 _102289 _102316 t f) = (term53 _102289 _102316 t f).
Proof. exact (MK_COMB (@lem4068200) (@lem4068199 _102289 _102316 t f)). Qed.
Lemma lem4068202 {_102289 _102316 : Type'} (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term54 _102289 _102316 P f t) = (term54 _102289 _102316 P f t).
Proof. exact (MK_COMB (@lem4068201 _102289 _102316 t f) (@lem4068180 _102289 _102316 P f t)). Qed.
Lemma lem4068205 {_102289 : Type'} (t : _102289 -> Prop) (s : _102289 -> Prop) : (term55 _102289 t s) = (term55 _102289 t s).
Proof. exact (eq_refl (term55 _102289 t s)). Qed.
Lemma lem4068206 {_102289 _102316 : Type'} (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term56 _102289 _102316 s P f t) = (term56 _102289 _102316 s P f t).
Proof. exact (MK_COMB (@lem4068205 _102289 t s) (@lem4068202 _102289 _102316 P f t)). Qed.
Lemma lem4068209 {_102289 : Type'} (t : _102289 -> Prop) (n : nat) : (term57 _102289 t n) = (term57 _102289 t n).
Proof. exact (eq_refl (term57 _102289 t n)). Qed.
Lemma lem4068210 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term58 _102289 _102316 n s P f t) = (term58 _102289 _102316 n s P f t).
Proof. exact (MK_COMB (@lem4068209 _102289 t n) (@lem4068206 _102289 _102316 s P f t)). Qed.
Lemma lem4068213 {_102289 : Type'} (t : _102289 -> Prop) : (term59 _102289 t) = (term59 _102289 t).
Proof. exact (eq_refl (term59 _102289 t)). Qed.
Lemma lem4068214 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term60 _102289 _102316 n s P f t) = (term60 _102289 _102316 n s P f t).
Proof. exact (MK_COMB (@lem4068213 _102289 t) (@lem4068210 _102289 _102316 n s P f t)). Qed.
Lemma lem4068215 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term61 _102289 _102316 n s P f) = (term61 _102289 _102316 n s P f).
Proof. exact (fun_ext (fun t : _102289 -> Prop => @lem4068214 _102289 _102316 n s P f t)). Qed.
Lemma lem4068216 {_102289 : Type'} : (@ex (_102289 -> Prop)) = (@ex (_102289 -> Prop)).
Proof. exact (eq_refl (@ex (_102289 -> Prop))). Qed.
Lemma lem4068217 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term15 _102289 _102316 n s P f) = (term15 _102289 _102316 n s P f).
Proof. exact (MK_COMB (@lem4068216 _102289) (@lem4068215 _102289 _102316 n s P f)). Qed.
Lemma lem4068218 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4068219 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term17 _102289 _102316 n s P f) = (term17 _102289 _102316 n s P f).
Proof. exact (MK_COMB (@lem4068218) (@lem4068217 _102289 _102316 n s P f)). Qed.
Lemma lem4068220 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term20 _102289 _102316 n s P f) = (term20 _102289 _102316 n s P f).
Proof. exact (MK_COMB (@lem4068219 _102289 _102316 n s P f) (@lem4068179 _102289 _102316 n s P f)). Qed.
Lemma lem4068221 {_102289 _102316 : Type'} (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term30 _102289 _102316 s P f) = (term30 _102289 _102316 s P f).
Proof. exact (fun_ext (fun n : nat => @lem4068220 _102289 _102316 n s P f)). Qed.
Lemma lem4068222 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4068223 {_102289 _102316 : Type'} (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term32 _102289 _102316 s P f) = (term32 _102289 _102316 s P f).
Proof. exact (MK_COMB (@lem4068222) (@lem4068221 _102289 _102316 s P f)). Qed.
Lemma lem4068224 {_102289 _102316 : Type'} (P : type686 _102316) (f : _102289 -> _102316) : (term34 _102289 _102316 P f) = (term34 _102289 _102316 P f).
Proof. exact (fun_ext (fun s : _102289 -> Prop => @lem4068223 _102289 _102316 s P f)). Qed.
Lemma lem4068225 {_102289 : Type'} : (@all (_102289 -> Prop)) = (@all (_102289 -> Prop)).
Proof. exact (eq_refl (@all (_102289 -> Prop))). Qed.
Lemma lem4068226 {_102289 _102316 : Type'} (P : type686 _102316) (f : _102289 -> _102316) : (term36 _102289 _102316 P f) = (term36 _102289 _102316 P f).
Proof. exact (MK_COMB (@lem4068225 _102289) (@lem4068224 _102289 _102316 P f)). Qed.
Lemma lem4068227 {_102289 _102316 : Type'} (f : _102289 -> _102316) : (term38 _102289 _102316 f) = (term38 _102289 _102316 f).
Proof. exact (fun_ext (fun P : type686 _102316 => @lem4068226 _102289 _102316 P f)). Qed.
Lemma lem4068228 {_102316 : Type'} : (@all ((_102316 -> Prop) -> Prop)) = (@all ((_102316 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_102316 -> Prop) -> Prop))). Qed.
Lemma lem4068229 {_102289 _102316 : Type'} (f : _102289 -> _102316) : (term40 _102289 _102316 f) = (term40 _102289 _102316 f).
Proof. exact (MK_COMB (@lem4068228 _102316) (@lem4068227 _102289 _102316 f)). Qed.
Lemma lem4068230 {_102289 _102316 : Type'} : (term42 _102289 _102316) = (term42 _102289 _102316).
Proof. exact (fun_ext (fun f : _102289 -> _102316 => @lem4068229 _102289 _102316 f)). Qed.
Lemma lem4068231 {_102289 _102316 : Type'} : (@all (_102289 -> _102316)) = (@all (_102289 -> _102316)).
Proof. exact (eq_refl (@all (_102289 -> _102316))). Qed.
Lemma lem4068232 {_102289 _102316 : Type'} : (term44 _102289 _102316) = (term44 _102289 _102316).
Proof. exact (MK_COMB (@lem4068231 _102289 _102316) (@lem4068230 _102289 _102316)). Qed.
Lemma lem4068303 {_102289 _102316 : Type'} : (term43 _102289 _102316) = (term44 _102289 _102316).
Proof. exact (TRANS (@lem4068163 _102289 _102316) (@lem4068232 _102289 _102316)). Qed.
Lemma lem4068304 {_102289 _102316 : Type'} : (term44 _102289 _102316) = (term43 _102289 _102316).
Proof. exact (SYM (@lem4068303 _102289 _102316)). Qed.
Lemma lem4068305 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (h1 : term15 _102289 _102316 n s P f) : term15 _102289 _102316 n s P f.
Proof. exact (h1). Qed.
Lemma lem4068307 (p : Prop) : p = (term21 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4068308 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term18 _102289 _102316 n s P f) = (term62 _102289 _102316 n s P f).
Proof. exact (@lem4068307 (term18 _102289 _102316 n s P f)). Qed.
Lemma lem4068309 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term62 _102289 _102316 n s P f) = (term18 _102289 _102316 n s P f).
Proof. exact (SYM (@lem4068308 _102289 _102316 n s P f)). Qed.
Lemma lem4068310 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (h1 : term63 _102289 _102316 n s P f) : term63 _102289 _102316 n s P f.
Proof. exact (h1). Qed.
Lemma lem4068320 {_102289 : Type'} (x : _102289) (y : _102289) (t : _102289 -> Prop) : (term64 _102289 x y t) = (term65 _102289 x y t).
Proof. exact (@lem17045 (@IN _102289 x t) (@IN _102289 y t)). Qed.
Lemma lem4068335 {_102289 _102316 : Type'} (f : _102289 -> _102316) (x : _102289) (y : _102289) : (((f x) = (f y)) = (x = y)) = (term66 _102289 _102316 f x y).
Proof. exact (@lem17784 ((f x) = (f y)) (x = y)). Qed.
Lemma lem4068336 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4068337 {_102289 : Type'} (x : _102289) (y : _102289) (t : _102289 -> Prop) : (term67 _102289 x y t) = (term68 _102289 x y t).
Proof. exact (MK_COMB (@lem4068336) (@lem4068320 _102289 x y t)). Qed.
Lemma lem4068338 {_102289 _102316 : Type'} (t : _102289 -> Prop) (f : _102289 -> _102316) (x : _102289) (y : _102289) : (term69 _102289 _102316 t f x y) = (term70 _102289 _102316 t f x y).
Proof. exact (MK_COMB (@lem4068337 _102289 x y t) (@lem4068335 _102289 _102316 f x y)). Qed.
Lemma lem4068339 {_102289 _102316 : Type'} (t : _102289 -> Prop) (f : _102289 -> _102316) (x : _102289) (y : _102289) : (term48 _102289 _102316 t f x y) = (term69 _102289 _102316 t f x y).
Proof. exact (@lem17265 (term71 _102289 x y t) (((f x) = (f y)) = (x = y))). Qed.
Lemma lem4068340 {_102289 _102316 : Type'} (t : _102289 -> Prop) (f : _102289 -> _102316) (x : _102289) (y : _102289) : (term48 _102289 _102316 t f x y) = (term70 _102289 _102316 t f x y).
Proof. exact (TRANS (@lem4068339 _102289 _102316 t f x y) (@lem4068338 _102289 _102316 t f x y)). Qed.
Lemma lem4068341 {_102289 _102316 : Type'} (t : _102289 -> Prop) (f : _102289 -> _102316) (x : _102289) : (term49 _102289 _102316 t f x) = (term72 _102289 _102316 t f x).
Proof. exact (fun_ext (fun y : _102289 => @lem4068340 _102289 _102316 t f x y)). Qed.
Lemma lem4068342 {_102289 : Type'} : (@all _102289) = (@all _102289).
Proof. exact (eq_refl (@all _102289)). Qed.
Lemma lem4068343 {_102289 _102316 : Type'} (t : _102289 -> Prop) (f : _102289 -> _102316) (x : _102289) : (term50 _102289 _102316 t f x) = (term73 _102289 _102316 t f x).
Proof. exact (MK_COMB (@lem4068342 _102289) (@lem4068341 _102289 _102316 t f x)). Qed.
Lemma lem4068344 {_102289 _102316 : Type'} (t : _102289 -> Prop) (f : _102289 -> _102316) : (term51 _102289 _102316 t f) = (term74 _102289 _102316 t f).
Proof. exact (fun_ext (fun x : _102289 => @lem4068343 _102289 _102316 t f x)). Qed.
Lemma lem4068345 {_102289 : Type'} : (@all _102289) = (@all _102289).
Proof. exact (eq_refl (@all _102289)). Qed.
Lemma lem4068346 {_102289 _102316 : Type'} (t : _102289 -> Prop) (f : _102289 -> _102316) : (term52 _102289 _102316 t f) = (term75 _102289 _102316 t f).
Proof. exact (MK_COMB (@lem4068345 _102289) (@lem4068344 _102289 _102316 t f)). Qed.
Lemma lem4068347 {_102289 _102316 : Type'} (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term47 _102289 _102316 P f t) = (term47 _102289 _102316 P f t).
Proof. exact (eq_refl (term47 _102289 _102316 P f t)). Qed.
Lemma lem4068348 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4068349 {_102289 _102316 : Type'} (t : _102289 -> Prop) (f : _102289 -> _102316) : (term53 _102289 _102316 t f) = (term76 _102289 _102316 t f).
Proof. exact (MK_COMB (@lem4068348) (@lem4068346 _102289 _102316 t f)). Qed.
Lemma lem4068350 {_102289 _102316 : Type'} (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term54 _102289 _102316 P f t) = (term77 _102289 _102316 P f t).
Proof. exact (MK_COMB (@lem4068349 _102289 _102316 t f) (@lem4068347 _102289 _102316 P f t)). Qed.
Lemma lem4068352 {_102289 : Type'} (t : _102289 -> Prop) (s : _102289 -> Prop) : (term55 _102289 t s) = (term55 _102289 t s).
Proof. exact (eq_refl (term55 _102289 t s)). Qed.
Lemma lem4068353 {_102289 _102316 : Type'} (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term56 _102289 _102316 s P f t) = (term78 _102289 _102316 s P f t).
Proof. exact (MK_COMB (@lem4068352 _102289 t s) (@lem4068350 _102289 _102316 P f t)). Qed.
Lemma lem4068355 {_102289 : Type'} (t : _102289 -> Prop) (n : nat) : (term57 _102289 t n) = (term57 _102289 t n).
Proof. exact (eq_refl (term57 _102289 t n)). Qed.
Lemma lem4068356 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term58 _102289 _102316 n s P f t) = (term79 _102289 _102316 n s P f t).
Proof. exact (MK_COMB (@lem4068355 _102289 t n) (@lem4068353 _102289 _102316 s P f t)). Qed.
Lemma lem4068358 {_102289 : Type'} (t : _102289 -> Prop) : (term59 _102289 t) = (term59 _102289 t).
Proof. exact (eq_refl (term59 _102289 t)). Qed.
Lemma lem4068359 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term60 _102289 _102316 n s P f t) = (term80 _102289 _102316 n s P f t).
Proof. exact (MK_COMB (@lem4068358 _102289 t) (@lem4068356 _102289 _102316 n s P f t)). Qed.
Lemma lem4068360 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term61 _102289 _102316 n s P f) = (term81 _102289 _102316 n s P f).
Proof. exact (fun_ext (fun t : _102289 -> Prop => @lem4068359 _102289 _102316 n s P f t)). Qed.
Lemma lem4068361 {_102289 : Type'} : (@ex (_102289 -> Prop)) = (@ex (_102289 -> Prop)).
Proof. exact (eq_refl (@ex (_102289 -> Prop))). Qed.
Lemma lem4068446 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term15 _102289 _102316 n s P f) = (term82 _102289 _102316 n s P f).
Proof. exact (MK_COMB (@lem4068361 _102289) (@lem4068360 _102289 _102316 n s P f)). Qed.
Lemma lem4068447 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (h1 : term15 _102289 _102316 n s P f) : term82 _102289 _102316 n s P f.
Proof. exact (EQ_MP (@lem4068446 _102289 _102316 n s P f) (@lem4068305 _102289 _102316 n s P f h1)). Qed.
Lemma lem4068456 {_102289 _102316 : Type'} (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term83 _102289 _102316 s P f t) = (term84 _102289 _102316 s P f t).
Proof. exact (@lem17045 (@SUBSET _102289 t s) (term47 _102289 _102316 P f t)). Qed.
Lemma lem4068458 {_102289 : Type'} (t : _102289 -> Prop) (n : nat) : (term85 _102289 t n) = (term85 _102289 t n).
Proof. exact (eq_refl (term85 _102289 t n)). Qed.
Lemma lem4068459 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term86 _102289 _102316 n s P f t) = (term87 _102289 _102316 n s P f t).
Proof. exact (MK_COMB (@lem4068458 _102289 t n) (@lem4068456 _102289 _102316 s P f t)). Qed.
Lemma lem4068460 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term88 _102289 _102316 n s P f t) = (term86 _102289 _102316 n s P f t).
Proof. exact (@lem17045 (term89 _102289 t n) (term90 _102289 _102316 s P f t)). Qed.
Lemma lem4068461 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term88 _102289 _102316 n s P f t) = (term87 _102289 _102316 n s P f t).
Proof. exact (TRANS (@lem4068460 _102289 _102316 n s P f t) (@lem4068459 _102289 _102316 n s P f t)). Qed.
Lemma lem4068463 {_102289 : Type'} (t : _102289 -> Prop) : (term91 _102289 t) = (term91 _102289 t).
Proof. exact (eq_refl (term91 _102289 t)). Qed.
Lemma lem4068464 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term92 _102289 _102316 n s P f t) = (term93 _102289 _102316 n s P f t).
Proof. exact (MK_COMB (@lem4068463 _102289 t) (@lem4068461 _102289 _102316 n s P f t)). Qed.
Lemma lem4068465 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term94 _102289 _102316 n s P f t) = (term92 _102289 _102316 n s P f t).
Proof. exact (@lem17045 (@FINITE _102289 t) (term95 _102289 _102316 n s P f t)). Qed.
Lemma lem4068466 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term94 _102289 _102316 n s P f t) = (term93 _102289 _102316 n s P f t).
Proof. exact (TRANS (@lem4068465 _102289 _102316 n s P f t) (@lem4068464 _102289 _102316 n s P f t)). Qed.
Lemma lem4068467 {_102289 : Type'} (P : type686 _102289) : (term96 _102289 P) = (term97 _102289 P).
Proof. exact (@lem18394 (_102289 -> Prop) P). Qed.
Lemma lem4068468 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term63 _102289 _102316 n s P f) = (term98 _102289 _102316 n s P f).
Proof. exact (@lem4068467 _102289 (term46 _102289 _102316 n s P f)). Qed.
Lemma lem4068469 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term99 _102289 _102316 n s P f t) = (term45 _102289 _102316 n s P f t).
Proof. exact (eq_refl (term99 _102289 _102316 n s P f t)). Qed.
Lemma lem4068470 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4068471 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term100 _102289 _102316 n s P f t) = (term94 _102289 _102316 n s P f t).
Proof. exact (MK_COMB (@lem4068470) (@lem4068469 _102289 _102316 n s P f t)). Qed.
Lemma lem4068472 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term100 _102289 _102316 n s P f t) = (term93 _102289 _102316 n s P f t).
Proof. exact (TRANS (@lem4068471 _102289 _102316 n s P f t) (@lem4068466 _102289 _102316 n s P f t)). Qed.
Lemma lem4068473 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term101 _102289 _102316 n s P f) = (term102 _102289 _102316 n s P f).
Proof. exact (fun_ext (fun t : _102289 -> Prop => @lem4068472 _102289 _102316 n s P f t)). Qed.
Lemma lem4068474 {_102289 : Type'} : (@all (_102289 -> Prop)) = (@all (_102289 -> Prop)).
Proof. exact (eq_refl (@all (_102289 -> Prop))). Qed.
Lemma lem4068475 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term98 _102289 _102316 n s P f) = (term103 _102289 _102316 n s P f).
Proof. exact (MK_COMB (@lem4068474 _102289) (@lem4068473 _102289 _102316 n s P f)). Qed.
Lemma lem4068528 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term63 _102289 _102316 n s P f) = (term103 _102289 _102316 n s P f).
Proof. exact (TRANS (@lem4068468 _102289 _102316 n s P f) (@lem4068475 _102289 _102316 n s P f)). Qed.
Lemma lem4068529 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (h1 : term63 _102289 _102316 n s P f) : term103 _102289 _102316 n s P f.
Proof. exact (EQ_MP (@lem4068528 _102289 _102316 n s P f) (@lem4068310 _102289 _102316 n s P f h1)). Qed.
Lemma lem4068530 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) (h1 : term80 _102289 _102316 n s P f t) : term80 _102289 _102316 n s P f t.
Proof. exact (h1). Qed.
Lemma lem4068569 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term93 _102289 _102316 n s P f t) = (term93 _102289 _102316 n s P f t).
Proof. exact (eq_refl (term93 _102289 _102316 n s P f t)). Qed.
Lemma lem4068570 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term102 _102289 _102316 n s P f) = (term102 _102289 _102316 n s P f).
Proof. exact (fun_ext (fun t : _102289 -> Prop => @lem4068569 _102289 _102316 n s P f t)). Qed.
Lemma lem4068571 {_102289 : Type'} : (@all (_102289 -> Prop)) = (@all (_102289 -> Prop)).
Proof. exact (eq_refl (@all (_102289 -> Prop))). Qed.
Lemma lem4068572 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term103 _102289 _102316 n s P f) = (term103 _102289 _102316 n s P f).
Proof. exact (MK_COMB (@lem4068571 _102289) (@lem4068570 _102289 _102316 n s P f)). Qed.
Lemma lem4068573 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (h1 : term63 _102289 _102316 n s P f) : term103 _102289 _102316 n s P f.
Proof. exact (EQ_MP (@lem4068572 _102289 _102316 n s P f) (@lem4068529 _102289 _102316 n s P f h1)). Qed.
Lemma lem4068580 {_102289 _102316 : Type'} (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term47 _102289 _102316 P f t) = (term47 _102289 _102316 P f t).
Proof. exact (eq_refl (term47 _102289 _102316 P f t)). Qed.
Lemma lem4068585 {_102289 : Type'} (x : _102289) (y : _102289) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4068586 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4068587 {_102316 : Type'} : (@eq _102316) = (@eq _102316).
Proof. exact (eq_refl (@eq _102316)). Qed.
Lemma lem4068592 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4068594 {_102289 _102316 : Type'} (f : _102289 -> _102316) (x : _102289) : (f x) = (@I (_102289 -> _102316) f x).
Proof. exact (@lem4068592 _102289 _102316 f x). Qed.
Lemma lem4068599 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4068600 {_102289 _102316 : Type'} (f : _102289 -> _102316) (x : _102289) : (f x) = (@I (_102289 -> _102316) f x).
Proof. exact (@lem4068599 _102289 _102316 f x). Qed.
Lemma lem4068602 {_102289 _102316 : Type'} (f : _102289 -> _102316) (y : _102289) : (f y) = (@I (_102289 -> _102316) f y).
Proof. exact (@lem4068600 _102289 _102316 f y). Qed.
Lemma lem4068603 {_102289 _102316 : Type'} (f : _102289 -> _102316) (x : _102289) : (term104 _102289 _102316 f x) = (term105 _102289 _102316 f x).
Proof. exact (MK_COMB (@lem4068587 _102316) (@lem4068594 _102289 _102316 f x)). Qed.
Lemma lem4068604 {_102289 _102316 : Type'} (x : _102289) (f : _102289 -> _102316) (y : _102289) : ((f x) = (f y)) = ((@I (_102289 -> _102316) f x) = (@I (_102289 -> _102316) f y)).
Proof. exact (MK_COMB (@lem4068603 _102289 _102316 f x) (@lem4068602 _102289 _102316 f y)). Qed.
Lemma lem4068605 {_102289 _102316 : Type'} (x : _102289) (f : _102289 -> _102316) (y : _102289) : (term106 _102289 _102316 x f y) = (term107 _102289 _102316 x f y).
Proof. exact (MK_COMB (@lem4068586) (@lem4068604 _102289 _102316 x f y)). Qed.
Lemma lem4068606 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4068607 {_102289 _102316 : Type'} (x : _102289) (f : _102289 -> _102316) (y : _102289) : (term108 _102289 _102316 x f y) = (term109 _102289 _102316 x f y).
Proof. exact (MK_COMB (@lem4068606) (@lem4068605 _102289 _102316 x f y)). Qed.
Lemma lem4068608 {_102289 _102316 : Type'} (f : _102289 -> _102316) (x : _102289) (y : _102289) : (term110 _102289 _102316 f x y) = (term111 _102289 _102316 f x y).
Proof. exact (MK_COMB (@lem4068607 _102289 _102316 x f y) (@lem4068585 _102289 x y)). Qed.
Lemma lem4068615 {_102289 : Type'} (x : _102289) (y : _102289) : (term112 _102289 x y) = (term112 _102289 x y).
Proof. exact (eq_refl (term112 _102289 x y)). Qed.
Lemma lem4068616 {_102316 : Type'} : (@eq _102316) = (@eq _102316).
Proof. exact (eq_refl (@eq _102316)). Qed.
Lemma lem4068621 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4068623 {_102289 _102316 : Type'} (f : _102289 -> _102316) (x : _102289) : (f x) = (@I (_102289 -> _102316) f x).
Proof. exact (@lem4068621 _102289 _102316 f x). Qed.
Lemma lem4068628 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4068629 {_102289 _102316 : Type'} (f : _102289 -> _102316) (x : _102289) : (f x) = (@I (_102289 -> _102316) f x).
Proof. exact (@lem4068628 _102289 _102316 f x). Qed.
Lemma lem4068631 {_102289 _102316 : Type'} (f : _102289 -> _102316) (y : _102289) : (f y) = (@I (_102289 -> _102316) f y).
Proof. exact (@lem4068629 _102289 _102316 f y). Qed.
Lemma lem4068632 {_102289 _102316 : Type'} (f : _102289 -> _102316) (x : _102289) : (term104 _102289 _102316 f x) = (term105 _102289 _102316 f x).
Proof. exact (MK_COMB (@lem4068616 _102316) (@lem4068623 _102289 _102316 f x)). Qed.
Lemma lem4068633 {_102289 _102316 : Type'} (x : _102289) (f : _102289 -> _102316) (y : _102289) : ((f x) = (f y)) = ((@I (_102289 -> _102316) f x) = (@I (_102289 -> _102316) f y)).
Proof. exact (MK_COMB (@lem4068632 _102289 _102316 f x) (@lem4068631 _102289 _102316 f y)). Qed.
Lemma lem4068634 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4068635 {_102289 _102316 : Type'} (x : _102289) (f : _102289 -> _102316) (y : _102289) : (term113 _102289 _102316 x f y) = (term114 _102289 _102316 x f y).
Proof. exact (MK_COMB (@lem4068634) (@lem4068633 _102289 _102316 x f y)). Qed.
Lemma lem4068636 {_102289 _102316 : Type'} (f : _102289 -> _102316) (x : _102289) (y : _102289) : (term115 _102289 _102316 f x y) = (term116 _102289 _102316 f x y).
Proof. exact (MK_COMB (@lem4068635 _102289 _102316 x f y) (@lem4068615 _102289 x y)). Qed.
Lemma lem4068637 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4068638 {_102289 _102316 : Type'} (f : _102289 -> _102316) (x : _102289) (y : _102289) : (term117 _102289 _102316 f x y) = (term118 _102289 _102316 f x y).
Proof. exact (MK_COMB (@lem4068637) (@lem4068636 _102289 _102316 f x y)). Qed.
Lemma lem4068639 {_102289 _102316 : Type'} (f : _102289 -> _102316) (x : _102289) (y : _102289) : (term66 _102289 _102316 f x y) = (term119 _102289 _102316 f x y).
Proof. exact (MK_COMB (@lem4068638 _102289 _102316 f x y) (@lem4068608 _102289 _102316 f x y)). Qed.
Lemma lem4068658 {_102289 : Type'} (x : _102289) (y : _102289) (t : _102289 -> Prop) : (term68 _102289 x y t) = (term68 _102289 x y t).
Proof. exact (eq_refl (term68 _102289 x y t)). Qed.
Lemma lem4068659 {_102289 _102316 : Type'} (t : _102289 -> Prop) (f : _102289 -> _102316) (x : _102289) (y : _102289) : (term70 _102289 _102316 t f x y) = (term120 _102289 _102316 t f x y).
Proof. exact (MK_COMB (@lem4068658 _102289 x y t) (@lem4068639 _102289 _102316 f x y)). Qed.
Lemma lem4068660 {_102289 _102316 : Type'} (t : _102289 -> Prop) (f : _102289 -> _102316) (x : _102289) : (term72 _102289 _102316 t f x) = (term121 _102289 _102316 t f x).
Proof. exact (fun_ext (fun y : _102289 => @lem4068659 _102289 _102316 t f x y)). Qed.
Lemma lem4068661 {_102289 : Type'} : (@all _102289) = (@all _102289).
Proof. exact (eq_refl (@all _102289)). Qed.
Lemma lem4068662 {_102289 _102316 : Type'} (t : _102289 -> Prop) (f : _102289 -> _102316) (x : _102289) : (term73 _102289 _102316 t f x) = (term122 _102289 _102316 t f x).
Proof. exact (MK_COMB (@lem4068661 _102289) (@lem4068660 _102289 _102316 t f x)). Qed.
Lemma lem4068663 {_102289 _102316 : Type'} (t : _102289 -> Prop) (f : _102289 -> _102316) : (term74 _102289 _102316 t f) = (term123 _102289 _102316 t f).
Proof. exact (fun_ext (fun x : _102289 => @lem4068662 _102289 _102316 t f x)). Qed.
Lemma lem4068664 {_102289 : Type'} : (@all _102289) = (@all _102289).
Proof. exact (eq_refl (@all _102289)). Qed.
Lemma lem4068665 {_102289 _102316 : Type'} (t : _102289 -> Prop) (f : _102289 -> _102316) : (term75 _102289 _102316 t f) = (term124 _102289 _102316 t f).
Proof. exact (MK_COMB (@lem4068664 _102289) (@lem4068663 _102289 _102316 t f)). Qed.
Lemma lem4068666 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4068667 {_102289 _102316 : Type'} (t : _102289 -> Prop) (f : _102289 -> _102316) : (term76 _102289 _102316 t f) = (term125 _102289 _102316 t f).
Proof. exact (MK_COMB (@lem4068666) (@lem4068665 _102289 _102316 t f)). Qed.
Lemma lem4068668 {_102289 _102316 : Type'} (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term77 _102289 _102316 P f t) = (term126 _102289 _102316 P f t).
Proof. exact (MK_COMB (@lem4068667 _102289 _102316 t f) (@lem4068580 _102289 _102316 P f t)). Qed.
Lemma lem4068675 {_102289 : Type'} (t : _102289 -> Prop) (s : _102289 -> Prop) : (term55 _102289 t s) = (term55 _102289 t s).
Proof. exact (eq_refl (term55 _102289 t s)). Qed.
Lemma lem4068676 {_102289 _102316 : Type'} (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term78 _102289 _102316 s P f t) = (term127 _102289 _102316 s P f t).
Proof. exact (MK_COMB (@lem4068675 _102289 t s) (@lem4068668 _102289 _102316 P f t)). Qed.
Lemma lem4068685 {_102289 : Type'} (t : _102289 -> Prop) (n : nat) : (term57 _102289 t n) = (term57 _102289 t n).
Proof. exact (eq_refl (term57 _102289 t n)). Qed.
Lemma lem4068686 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term79 _102289 _102316 n s P f t) = (term128 _102289 _102316 n s P f t).
Proof. exact (MK_COMB (@lem4068685 _102289 t n) (@lem4068676 _102289 _102316 s P f t)). Qed.
Lemma lem4068691 {_102289 : Type'} (t : _102289 -> Prop) : (term59 _102289 t) = (term59 _102289 t).
Proof. exact (eq_refl (term59 _102289 t)). Qed.
Lemma lem4068692 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term80 _102289 _102316 n s P f t) = (term129 _102289 _102316 n s P f t).
Proof. exact (MK_COMB (@lem4068691 _102289 t) (@lem4068686 _102289 _102316 n s P f t)). Qed.
Lemma lem4068693 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) (h1 : term80 _102289 _102316 n s P f t) : term129 _102289 _102316 n s P f t.
Proof. exact (EQ_MP (@lem4068692 _102289 _102316 n s P f t) (@lem4068530 _102289 _102316 n s P f t h1)). Qed.
Lemma lem4068694 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) (h1 : term80 _102289 _102316 n s P f t) : term128 _102289 _102316 n s P f t.
Proof. exact (proj2 (@lem4068693 _102289 _102316 n s P f t h1)). Qed.
Lemma lem4068696 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) (h1 : term80 _102289 _102316 n s P f t) : term127 _102289 _102316 s P f t.
Proof. exact (proj2 (@lem4068694 _102289 _102316 n s P f t h1)). Qed.
Lemma lem4068698 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) (h1 : term80 _102289 _102316 n s P f t) : term126 _102289 _102316 P f t.
Proof. exact (proj2 (@lem4068696 _102289 _102316 n s P f t h1)). Qed.
Lemma lem4068721 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term93 _102289 _102316 n s P f t) = (term93 _102289 _102316 n s P f t).
Proof. exact (eq_refl (term93 _102289 _102316 n s P f t)). Qed.
Lemma lem4068722 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term102 _102289 _102316 n s P f) = (term102 _102289 _102316 n s P f).
Proof. exact (fun_ext (fun t : _102289 -> Prop => @lem4068721 _102289 _102316 n s P f t)). Qed.
Lemma lem4068723 {_102289 : Type'} : (@all (_102289 -> Prop)) = (@all (_102289 -> Prop)).
Proof. exact (eq_refl (@all (_102289 -> Prop))). Qed.
Lemma lem4068725 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term103 _102289 _102316 n s P f) = (term103 _102289 _102316 n s P f).
Proof. exact (MK_COMB (@lem4068723 _102289) (@lem4068722 _102289 _102316 n s P f)). Qed.
Lemma lem4068726 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (h1 : term63 _102289 _102316 n s P f) : term103 _102289 _102316 n s P f.
Proof. exact (EQ_MP (@lem4068725 _102289 _102316 n s P f) (@lem4068573 _102289 _102316 n s P f h1)). Qed.
Lemma lem4068787 {_102289 _102316 : Type'} (_47775 : _102289 -> Prop) (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (h1 : term63 _102289 _102316 n s P f) : term130 _102289 _102316 n s P f _47775.
Proof. exact (@lem4068726 _102289 _102316 n s P f h1 _47775). Qed.
Lemma lem4068788 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (_47775 : _102289 -> Prop) : (term130 _102289 _102316 n s P f _47775) = (term93 _102289 _102316 n s P f _47775).
Proof. exact (eq_refl (term130 _102289 _102316 n s P f _47775)). Qed.
Lemma lem4068811 {_102289 _102316 : Type'} (_47775 : _102289 -> Prop) (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (h1 : term63 _102289 _102316 n s P f) : term93 _102289 _102316 n s P f _47775.
Proof. exact (EQ_MP (@lem4068788 _102289 _102316 n s P f _47775) (@lem4068787 _102289 _102316 _47775 n s P f h1)). Qed.
Lemma lem4068984 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) (h1 : term80 _102289 _102316 n s P f t) : @FINITE _102289 t.
Proof. exact (proj1 (@lem4068693 _102289 _102316 n s P f t h1)). Qed.
Lemma lem4068985 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) (h1 : term80 _102289 _102316 n s P f t) : term131 _102289 t.
Proof. exact (fun h0 : term132 _102289 t => @lem4068984 _102289 _102316 n s P f t h1). Qed.
Lemma lem4068987 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4068988 {_102289 : Type'} (t : _102289 -> Prop) : (term131 _102289 t) = (@FINITE _102289 t).
Proof. exact (@lem4068987 (@FINITE _102289 t)). Qed.
Lemma lem4068989 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) (h1 : term80 _102289 _102316 n s P f t) : @FINITE _102289 t.
Proof. exact (EQ_MP (@lem4068988 _102289 t) (@lem4068985 _102289 _102316 n s P f t h1)). Qed.
Lemma lem4068991 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) (h1 : term80 _102289 _102316 n s P f t) : term89 _102289 t n.
Proof. exact (proj1 (@lem4068694 _102289 _102316 n s P f t h1)). Qed.
Lemma lem4068992 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) (h1 : term80 _102289 _102316 n s P f t) : term134 _102289 t n.
Proof. exact (fun h0 : term135 _102289 t n => @lem4068991 _102289 _102316 n s P f t h1). Qed.
Lemma lem4068994 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4068995 {_102289 : Type'} (t : _102289 -> Prop) (n : nat) : (term134 _102289 t n) = (term89 _102289 t n).
Proof. exact (@lem4068994 (term89 _102289 t n)). Qed.
Lemma lem4068996 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) (h1 : term80 _102289 _102316 n s P f t) : term89 _102289 t n.
Proof. exact (EQ_MP (@lem4068995 _102289 t n) (@lem4068992 _102289 _102316 n s P f t h1)). Qed.
Lemma lem4068998 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) (h1 : term80 _102289 _102316 n s P f t) : @SUBSET _102289 t s.
Proof. exact (proj1 (@lem4068696 _102289 _102316 n s P f t h1)). Qed.
Lemma lem4068999 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) (h1 : term80 _102289 _102316 n s P f t) : term136 _102289 t s.
Proof. exact (fun h0 : term137 _102289 t s => @lem4068998 _102289 _102316 n s P f t h1). Qed.
Lemma lem4069001 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4069002 {_102289 : Type'} (t : _102289 -> Prop) (s : _102289 -> Prop) : (term136 _102289 t s) = (@SUBSET _102289 t s).
Proof. exact (@lem4069001 (@SUBSET _102289 t s)). Qed.
Lemma lem4069003 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) (h1 : term80 _102289 _102316 n s P f t) : @SUBSET _102289 t s.
Proof. exact (EQ_MP (@lem4069002 _102289 t s) (@lem4068999 _102289 _102316 n s P f t h1)). Qed.
Lemma lem4069005 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) (h1 : term80 _102289 _102316 n s P f t) : term47 _102289 _102316 P f t.
Proof. exact (proj2 (@lem4068698 _102289 _102316 n s P f t h1)). Qed.
Lemma lem4069006 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) (h1 : term80 _102289 _102316 n s P f t) : term138 _102289 _102316 P f t.
Proof. exact (fun h0 : term139 _102289 _102316 P f t => @lem4069005 _102289 _102316 n s P f t h1). Qed.
Lemma lem4069008 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4069009 {_102289 _102316 : Type'} (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term138 _102289 _102316 P f t) = (term47 _102289 _102316 P f t).
Proof. exact (@lem4069008 (term47 _102289 _102316 P f t)). Qed.
Lemma lem4069010 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) (h1 : term80 _102289 _102316 n s P f t) : term47 _102289 _102316 P f t.
Proof. exact (EQ_MP (@lem4069009 _102289 _102316 P f t) (@lem4069006 _102289 _102316 n s P f t h1)). Qed.
Lemma lem4069012 (a : Prop) (b : Prop) : (term140 a b) = (term141 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4069013 {_102289 _102316 : Type'} (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (_47775 : _102289 -> Prop) : (term84 _102289 _102316 s P f _47775) = (term83 _102289 _102316 s P f _47775).
Proof. exact (@lem4069012 (@SUBSET _102289 _47775 s) (term47 _102289 _102316 P f _47775)). Qed.
Lemma lem4069014 {_102289 : Type'} (_47775 : _102289 -> Prop) (n : nat) : (term85 _102289 _47775 n) = (term85 _102289 _47775 n).
Proof. exact (eq_refl (term85 _102289 _47775 n)). Qed.
Lemma lem4069015 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (_47775 : _102289 -> Prop) : (term87 _102289 _102316 n s P f _47775) = (term86 _102289 _102316 n s P f _47775).
Proof. exact (MK_COMB (@lem4069014 _102289 _47775 n) (@lem4069013 _102289 _102316 s P f _47775)). Qed.
Lemma lem4069017 (a : Prop) (b : Prop) : (term140 a b) = (term141 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4069018 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (_47775 : _102289 -> Prop) : (term86 _102289 _102316 n s P f _47775) = (term88 _102289 _102316 n s P f _47775).
Proof. exact (@lem4069017 (term89 _102289 _47775 n) (term90 _102289 _102316 s P f _47775)). Qed.
Lemma lem4069019 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (_47775 : _102289 -> Prop) : (term87 _102289 _102316 n s P f _47775) = (term88 _102289 _102316 n s P f _47775).
Proof. exact (TRANS (@lem4069015 _102289 _102316 n s P f _47775) (@lem4069018 _102289 _102316 n s P f _47775)). Qed.
Lemma lem4069020 {_102289 : Type'} (_47775 : _102289 -> Prop) : (term91 _102289 _47775) = (term91 _102289 _47775).
Proof. exact (eq_refl (term91 _102289 _47775)). Qed.
Lemma lem4069021 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (_47775 : _102289 -> Prop) : (term93 _102289 _102316 n s P f _47775) = (term92 _102289 _102316 n s P f _47775).
Proof. exact (MK_COMB (@lem4069020 _102289 _47775) (@lem4069019 _102289 _102316 n s P f _47775)). Qed.
Lemma lem4069023 (a : Prop) (b : Prop) : (term140 a b) = (term141 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4069024 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (_47775 : _102289 -> Prop) : (term92 _102289 _102316 n s P f _47775) = (term94 _102289 _102316 n s P f _47775).
Proof. exact (@lem4069023 (@FINITE _102289 _47775) (term95 _102289 _102316 n s P f _47775)). Qed.
Lemma lem4069025 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (_47775 : _102289 -> Prop) : (term93 _102289 _102316 n s P f _47775) = (term94 _102289 _102316 n s P f _47775).
Proof. exact (TRANS (@lem4069021 _102289 _102316 n s P f _47775) (@lem4069024 _102289 _102316 n s P f _47775)). Qed.
Lemma lem4069027 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4069028 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (_47775 : _102289 -> Prop) : (term94 _102289 _102316 n s P f _47775) = (term142 _102289 _102316 n s P f _47775).
Proof. exact (@lem4069027 (term45 _102289 _102316 n s P f _47775)). Qed.
Lemma lem4069029 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (_47775 : _102289 -> Prop) : (term93 _102289 _102316 n s P f _47775) = (term142 _102289 _102316 n s P f _47775).
Proof. exact (TRANS (@lem4069025 _102289 _102316 n s P f _47775) (@lem4069028 _102289 _102316 n s P f _47775)). Qed.
Lemma lem4069031 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) (h1 : term80 _102289 _102316 n s P f t) : term90 _102289 _102316 s P f t.
Proof. exact (conj (@lem4069003 _102289 _102316 n s P f t h1) (@lem4069010 _102289 _102316 n s P f t h1)). Qed.
Lemma lem4069032 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) (h1 : term80 _102289 _102316 n s P f t) : term95 _102289 _102316 n s P f t.
Proof. exact (conj (@lem4068996 _102289 _102316 n s P f t h1) (@lem4069031 _102289 _102316 n s P f t h1)). Qed.
Lemma lem4069033 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) (h1 : term80 _102289 _102316 n s P f t) : term45 _102289 _102316 n s P f t.
Proof. exact (conj (@lem4068989 _102289 _102316 n s P f t h1) (@lem4069032 _102289 _102316 n s P f t h1)). Qed.
Lemma lem4069035 {_102289 _102316 : Type'} (_47775 : _102289 -> Prop) (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (h1 : term63 _102289 _102316 n s P f) : term142 _102289 _102316 n s P f _47775.
Proof. exact (EQ_MP (@lem4069029 _102289 _102316 n s P f _47775) (@lem4068811 _102289 _102316 _47775 n s P f h1)). Qed.
Lemma lem4069036 {_102289 _102316 : Type'} (_47775 : _102289 -> Prop) (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (h1 : term63 _102289 _102316 n s P f) : term142 _102289 _102316 n s P f _47775.
Proof. exact (@lem4069035 _102289 _102316 _47775 n s P f h1). Qed.
Lemma lem4069037 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (h1 : term63 _102289 _102316 n s P f) : term142 _102289 _102316 n s P f t.
Proof. exact (@lem4069036 _102289 _102316 t n s P f h1). Qed.
Lemma lem4069040 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) (h1 : term63 _102289 _102316 n s P f) (h2 : term80 _102289 _102316 n s P f t) : False.
Proof. exact (@lem4069037 _102289 _102316 t n s P f h1 (@lem4069033 _102289 _102316 n s P f t h2)). Qed.
Lemma lem4069041 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) (h1 : term63 _102289 _102316 n s P f) (h2 : term80 _102289 _102316 n s P f t) : term143.
Proof. exact (fun h0 : ~ False => @lem4069040 _102289 _102316 n s P f t h1 h2). Qed.
Lemma lem4069043 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4069044 : term143 = False.
Proof. exact (@lem4069043 False). Qed.
Lemma lem4069045 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) (h1 : term63 _102289 _102316 n s P f) (h2 : term80 _102289 _102316 n s P f t) : False.
Proof. exact (EQ_MP (@lem4069044) (@lem4069041 _102289 _102316 n s P f t h1 h2)). Qed.
Lemma lem4069046 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (h1 : term15 _102289 _102316 n s P f) (h2 : term63 _102289 _102316 n s P f) : False.
Proof. exact (ex_elim (@lem4068447 _102289 _102316 n s P f h1) (fun t : _102289 -> Prop => fun h0 : term81 _102289 _102316 n s P f t => @lem4069045 _102289 _102316 n s P f t h2 h0)). Qed.
Lemma lem4069047 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (h1 : term15 _102289 _102316 n s P f) (h2 : term63 _102289 _102316 n s P f) : (term63 _102289 _102316 n s P f) = False.
Proof. exact (prop_ext (fun h3 : term63 _102289 _102316 n s P f => @lem4069046 _102289 _102316 n s P f h1 h2) (fun h3 : False => @lem4068310 _102289 _102316 n s P f h2)). Qed.
Lemma lem4069048 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (h1 : term15 _102289 _102316 n s P f) (h2 : term63 _102289 _102316 n s P f) : False.
Proof. exact (EQ_MP (@lem4069047 _102289 _102316 n s P f h1 h2) (@lem4068310 _102289 _102316 n s P f h2)). Qed.
Lemma lem4069049 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (h1 : term15 _102289 _102316 n s P f) : term62 _102289 _102316 n s P f.
Proof. exact (fun h0 : term63 _102289 _102316 n s P f => @lem4069048 _102289 _102316 n s P f h1 h0). Qed.
Lemma lem4069050 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (h1 : term15 _102289 _102316 n s P f) : term18 _102289 _102316 n s P f.
Proof. exact (EQ_MP (@lem4068309 _102289 _102316 n s P f) (@lem4069049 _102289 _102316 n s P f h1)). Qed.
Lemma lem4069051 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : term20 _102289 _102316 n s P f.
Proof. exact (fun h0 : term15 _102289 _102316 n s P f => @lem4069050 _102289 _102316 n s P f h0). Qed.
Lemma lem4069056 {_102289 _102316 : Type'} (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : term32 _102289 _102316 s P f.
Proof. exact (fun n : nat => @lem4069051 _102289 _102316 n s P f). Qed.
Lemma lem4069061 {_102289 _102316 : Type'} (P : type686 _102316) (f : _102289 -> _102316) : term36 _102289 _102316 P f.
Proof. exact (fun s : _102289 -> Prop => @lem4069056 _102289 _102316 s P f). Qed.
Lemma lem4069066 {_102289 _102316 : Type'} (f : _102289 -> _102316) : term40 _102289 _102316 f.
Proof. exact (fun P : type686 _102316 => @lem4069061 _102289 _102316 P f). Qed.
Lemma lem4069071 {_102289 _102316 : Type'} : term44 _102289 _102316.
Proof. exact (fun f : _102289 -> _102316 => @lem4069066 _102289 _102316 f). Qed.
Lemma lem4069072 {_102289 _102316 : Type'} : term43 _102289 _102316.
Proof. exact (EQ_MP (@lem4068304 _102289 _102316) (@lem4069071 _102289 _102316)). Qed.
Lemma lem4069073 {_102289 _102316 : Type'} (f : _102289 -> _102316) : term144 _102289 _102316 f.
Proof. exact (@lem4069072 _102289 _102316 f). Qed.
Lemma lem4069074 {_102289 _102316 : Type'} (f : _102289 -> _102316) : (term144 _102289 _102316 f) = (term39 _102289 _102316 f).
Proof. exact (eq_refl (term144 _102289 _102316 f)). Qed.
Lemma lem4069075 {_102289 _102316 : Type'} (f : _102289 -> _102316) : term39 _102289 _102316 f.
Proof. exact (EQ_MP (@lem4069074 _102289 _102316 f) (@lem4069073 _102289 _102316 f)). Qed.
Lemma lem4069076 {_102289 _102316 : Type'} (f : _102289 -> _102316) (P : type686 _102316) : term145 _102289 _102316 f P.
Proof. exact (@lem4069075 _102289 _102316 f P). Qed.
Lemma lem4069077 {_102289 _102316 : Type'} (P : type686 _102316) (f : _102289 -> _102316) : (term145 _102289 _102316 f P) = (term35 _102289 _102316 P f).
Proof. exact (eq_refl (term145 _102289 _102316 f P)). Qed.
Lemma lem4069078 {_102289 _102316 : Type'} (P : type686 _102316) (f : _102289 -> _102316) : term35 _102289 _102316 P f.
Proof. exact (EQ_MP (@lem4069077 _102289 _102316 P f) (@lem4069076 _102289 _102316 f P)). Qed.
Lemma lem4069079 {_102289 _102316 : Type'} (P : type686 _102316) (f : _102289 -> _102316) (s : _102289 -> Prop) : term146 _102289 _102316 P f s.
Proof. exact (@lem4069078 _102289 _102316 P f s). Qed.
Lemma lem4069080 {_102289 _102316 : Type'} (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term146 _102289 _102316 P f s) = (term31 _102289 _102316 s P f).
Proof. exact (eq_refl (term146 _102289 _102316 P f s)). Qed.
Lemma lem4069081 {_102289 _102316 : Type'} (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : term31 _102289 _102316 s P f.
Proof. exact (EQ_MP (@lem4069080 _102289 _102316 s P f) (@lem4069079 _102289 _102316 P f s)). Qed.
Lemma lem4069082 {_102289 _102316 : Type'} (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (n : nat) : term147 _102289 _102316 s P f n.
Proof. exact (@lem4069081 _102289 _102316 s P f n). Qed.
Lemma lem4069083 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term147 _102289 _102316 s P f n) = (term22 _102289 _102316 n s P f).
Proof. exact (eq_refl (term147 _102289 _102316 s P f n)). Qed.
Lemma lem4069084 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : term22 _102289 _102316 n s P f.
Proof. exact (EQ_MP (@lem4069083 _102289 _102316 n s P f) (@lem4069082 _102289 _102316 s P f n)). Qed.
Lemma lem4069086 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : term22 _102289 _102316 n s P f.
Proof. exact (@lem4068024 _102289 _102316 n s P f (@lem4069084 _102289 _102316 n s P f)). Qed.
Lemma lem4069087 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (h1 : term23 _102289 _102316 n s P f) : False.
Proof. exact (@lem4069086 _102289 _102316 n s P f (@lem4068008 _102289 _102316 n s P f h1)). Qed.
Lemma lem4069088 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (h1 : term23 _102289 _102316 n s P f) : (term23 _102289 _102316 n s P f) = False.
Proof. exact (prop_ext (fun h2 : term23 _102289 _102316 n s P f => @lem4069087 _102289 _102316 n s P f h1) (fun h2 : False => @lem4068008 _102289 _102316 n s P f h1)). Qed.
Lemma lem4069089 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (h1 : term23 _102289 _102316 n s P f) : False.
Proof. exact (EQ_MP (@lem4069088 _102289 _102316 n s P f h1) (@lem4068008 _102289 _102316 n s P f h1)). Qed.
Lemma lem4069090 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : term22 _102289 _102316 n s P f.
Proof. exact (fun h0 : term23 _102289 _102316 n s P f => @lem4069089 _102289 _102316 n s P f h0). Qed.
Lemma lem4069091 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : term20 _102289 _102316 n s P f.
Proof. exact (EQ_MP (@lem4068007 _102289 _102316 n s P f) (@lem4069090 _102289 _102316 n s P f)). Qed.
Lemma lem4069092 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : term19 _102289 _102316 n s P f.
Proof. exact (EQ_MP (@lem4068003 _102289 _102316 n s P f) (@lem4069091 _102289 _102316 n s P f)). Qed.
Lemma lem4069094 (p : Prop) : p = (term21 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4069095 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term148 _102289 _102316 n f s P) = (term149 _102289 _102316 n f s P).
Proof. exact (@lem4069094 (term148 _102289 _102316 n f s P)). Qed.
Lemma lem4069096 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term149 _102289 _102316 n f s P) = (term148 _102289 _102316 n f s P).
Proof. exact (SYM (@lem4069095 _102289 _102316 n f s P)). Qed.
Lemma lem4069097 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term150 _102289 _102316 n f s P) : term150 _102289 _102316 n f s P.
Proof. exact (h1). Qed.
Lemma lem4069098 {_102289 B : Type'} : term151 _102289 B.
Proof. exact (@lem3615104 _102289 B). Qed.
Lemma lem4069099 {_102316 B : Type'} : term151 _102316 B.
Proof. exact (@lem3615104 _102316 B). Qed.
Lemma lem4069100 {_102289 A : Type'} : term152 _102289 A.
Proof. exact (@lem3615104 A _102289). Qed.
Lemma lem4069101 {_102316 A : Type'} : term152 _102316 A.
Proof. exact (@lem3615104 A _102316). Qed.
Lemma lem4069102 {_102289 _102316 : Type'} : term151 _102289 _102316.
Proof. exact (@lem3615104 _102289 _102316). Qed.
Lemma lem4069103 {_102289 B : Type'} : term153 _102289 B.
Proof. exact (@lem4008003 _102289 B). Qed.
Lemma lem4069104 {_102316 B : Type'} : term153 _102316 B.
Proof. exact (@lem4008003 _102316 B). Qed.
Lemma lem4069105 {A B : Type'} : term153 A B.
Proof. exact (@lem4008003 A B). Qed.
Lemma lem4069106 {B : Type'} : term154 B.
Proof. exact (@lem4008003 B B). Qed.
Lemma lem4069107 {_102289 A : Type'} : term155 _102289 A.
Proof. exact (@lem4008003 A _102289). Qed.
Lemma lem4069108 {_102316 A : Type'} : term155 _102316 A.
Proof. exact (@lem4008003 A _102316). Qed.
Lemma lem4069109 {_102289 _102316 : Type'} : term153 _102289 _102316.
Proof. exact (@lem4008003 _102289 _102316). Qed.
Lemma lem4069116 {_102289 _87604 : Type'} : term156 _102289 _87604.
Proof. exact (@lem3371475 _102289 _87604). Qed.
Lemma lem4069117 {_102316 _87604 : Type'} : term156 _102316 _87604.
Proof. exact (@lem3371475 _102316 _87604). Qed.
Lemma lem4069118 {_102289 _87593 : Type'} : term157 _102289 _87593.
Proof. exact (@lem3371475 _87593 _102289). Qed.
Lemma lem4069119 {_102316 _87593 : Type'} : term157 _102316 _87593.
Proof. exact (@lem3371475 _87593 _102316). Qed.
Lemma lem4069120 {_102289 _102316 : Type'} : term156 _102289 _102316.
Proof. exact (@lem3371475 _102289 _102316). Qed.
Lemma lem4069121 {_102316 A : Type'} : term157 _102316 A.
Proof. exact (@lem3371475 A _102316). Qed.
Lemma lem4069122 {_102289 A : Type'} : term157 _102289 A.
Proof. exact (@lem3371475 A _102289). Qed.
Lemma lem4069123 {_102316 B : Type'} : term156 _102316 B.
Proof. exact (@lem3371475 _102316 B). Qed.
Lemma lem4069124 {_102289 B : Type'} : term156 _102289 B.
Proof. exact (@lem3371475 _102289 B). Qed.
Lemma lem4069125 {B : Type'} : term158 B.
Proof. exact (@lem3371475 B B). Qed.
Lemma lem4069126 {A B : Type'} : term156 A B.
Proof. exact (@lem3371475 A B). Qed.
Lemma lem4069129 {_102289 _102316 _87593 _87604 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term159 _102289 _102316 _87593 _87604 A B n f s P) : term159 _102289 _102316 _87593 _87604 A B n f s P.
Proof. exact (h1). Qed.
Lemma lem4069130 {_102289 _102316 _87593 _87604 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : term160 _102289 _102316 _87593 _87604 A B n f s P.
Proof. exact (fun h0 : term159 _102289 _102316 _87593 _87604 A B n f s P => @lem4069129 _102289 _102316 _87593 _87604 A B n f s P h0). Qed.
Lemma lem4069131 {_102289 _102316 _87593 _87604 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term160 _102289 _102316 _87593 _87604 A B n f s P) : term160 _102289 _102316 _87593 _87604 A B n f s P.
Proof. exact (h1). Qed.
Lemma lem4069132 {_102289 _102316 _87593 _87604 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term159 _102289 _102316 _87593 _87604 A B n f s P) : term159 _102289 _102316 _87593 _87604 A B n f s P.
Proof. exact (h1). Qed.
Lemma lem4069133 {_102289 _102316 _87593 _87604 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term159 _102289 _102316 _87593 _87604 A B n f s P) (h2 : term160 _102289 _102316 _87593 _87604 A B n f s P) : term159 _102289 _102316 _87593 _87604 A B n f s P.
Proof. exact (@lem4069131 _102289 _102316 _87593 _87604 A B n f s P h2 (@lem4069132 _102289 _102316 _87593 _87604 A B n f s P h1)). Qed.
Lemma lem4069134 {_102289 _102316 _87593 _87604 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term159 _102289 _102316 _87593 _87604 A B n f s P) : term161 _102289 _102316 _87593 _87604 A B n f s P.
Proof. exact (fun h0 : term160 _102289 _102316 _87593 _87604 A B n f s P => @lem4069133 _102289 _102316 _87593 _87604 A B n f s P h1 h0). Qed.
Lemma lem4069135 {_102289 _102316 _87593 _87604 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term160 _102289 _102316 _87593 _87604 A B n f s P) : term160 _102289 _102316 _87593 _87604 A B n f s P.
Proof. exact (h1). Qed.
Lemma lem4069136 {_102289 _102316 _87593 _87604 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term159 _102289 _102316 _87593 _87604 A B n f s P) (h2 : term160 _102289 _102316 _87593 _87604 A B n f s P) : term159 _102289 _102316 _87593 _87604 A B n f s P.
Proof. exact (@lem4069134 _102289 _102316 _87593 _87604 A B n f s P h1 (@lem4069135 _102289 _102316 _87593 _87604 A B n f s P h2)). Qed.
Lemma lem4069137 {_102289 _102316 _87593 _87604 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term160 _102289 _102316 _87593 _87604 A B n f s P) : term160 _102289 _102316 _87593 _87604 A B n f s P.
Proof. exact (fun h0 : term159 _102289 _102316 _87593 _87604 A B n f s P => @lem4069136 _102289 _102316 _87593 _87604 A B n f s P h0 h1). Qed.
Lemma lem4069138 {_102289 _102316 _87593 _87604 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : term162 _102289 _102316 _87593 _87604 A B n f s P.
Proof. exact (fun h0 : term160 _102289 _102316 _87593 _87604 A B n f s P => @lem4069137 _102289 _102316 _87593 _87604 A B n f s P h0). Qed.
Lemma lem4069141 {_102289 _102316 _87593 _87604 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : term160 _102289 _102316 _87593 _87604 A B n f s P.
Proof. exact (@lem4069138 _102289 _102316 _87593 _87604 A B n f s P (@lem4069130 _102289 _102316 _87593 _87604 A B n f s P)). Qed.
Lemma lem4069142 {_102289 _102316 _87593 _87604 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : term160 _102289 _102316 _87593 _87604 A B n f s P.
Proof. exact (@lem4069141 _102289 _102316 _87593 _87604 A B n f s P). Qed.
Lemma lem4069558 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4069559 {_102316 A : Type'} : (term163 _102316 A) = (term164 _102316 A).
Proof. exact (@lem4069558 (term152 _102316 A)). Qed.
Lemma lem4069570 {_102289 A : Type'} : (term165 _102289 A) = (term165 _102289 A).
Proof. exact (eq_refl (term165 _102289 A)). Qed.
Lemma lem4069571 {_102289 _102316 A : Type'} : (term166 _102289 _102316 A) = (term167 _102289 _102316 A).
Proof. exact (MK_COMB (@lem4069570 _102289 A) (@lem4069559 _102316 A)). Qed.
Lemma lem4069574 {_102316 B : Type'} : (term168 _102316 B) = (term168 _102316 B).
Proof. exact (eq_refl (term168 _102316 B)). Qed.
Lemma lem4069575 {_102289 _102316 A B : Type'} : (term169 _102289 _102316 A B) = (term170 _102289 _102316 A B).
Proof. exact (MK_COMB (@lem4069574 _102316 B) (@lem4069571 _102289 _102316 A)). Qed.
Lemma lem4069578 {_102289 B : Type'} : (term168 _102289 B) = (term168 _102289 B).
Proof. exact (eq_refl (term168 _102289 B)). Qed.
Lemma lem4069579 {_102289 _102316 A B : Type'} : (term171 _102289 _102316 A B) = (term172 _102289 _102316 A B).
Proof. exact (MK_COMB (@lem4069578 _102289 B) (@lem4069575 _102289 _102316 A B)). Qed.
Lemma lem4069582 {_102289 _102316 : Type'} : (term168 _102289 _102316) = (term168 _102289 _102316).
Proof. exact (eq_refl (term168 _102289 _102316)). Qed.
Lemma lem4069583 {_102289 _102316 A B : Type'} : (term173 _102289 _102316 A B) = (term174 _102289 _102316 A B).
Proof. exact (MK_COMB (@lem4069582 _102289 _102316) (@lem4069579 _102289 _102316 A B)). Qed.
Lemma lem4069586 {B : Type'} : (term175 B) = (term175 B).
Proof. exact (eq_refl (term175 B)). Qed.
Lemma lem4069587 {_102289 _102316 A B : Type'} : (term176 _102289 _102316 A B) = (term177 _102289 _102316 A B).
Proof. exact (MK_COMB (@lem4069586 B) (@lem4069583 _102289 _102316 A B)). Qed.
Lemma lem4069590 {A B : Type'} : (term178 A B) = (term178 A B).
Proof. exact (eq_refl (term178 A B)). Qed.
Lemma lem4069591 {_102289 _102316 A B : Type'} : (term179 _102289 _102316 A B) = (term180 _102289 _102316 A B).
Proof. exact (MK_COMB (@lem4069590 A B) (@lem4069587 _102289 _102316 A B)). Qed.
Lemma lem4069594 {_102316 A : Type'} : (term181 _102316 A) = (term181 _102316 A).
Proof. exact (eq_refl (term181 _102316 A)). Qed.
Lemma lem4069595 {_102289 _102316 A B : Type'} : (term182 _102289 _102316 A B) = (term183 _102289 _102316 A B).
Proof. exact (MK_COMB (@lem4069594 _102316 A) (@lem4069591 _102289 _102316 A B)). Qed.
Lemma lem4069598 {_102289 A : Type'} : (term181 _102289 A) = (term181 _102289 A).
Proof. exact (eq_refl (term181 _102289 A)). Qed.
Lemma lem4069599 {_102289 _102316 A B : Type'} : (term184 _102289 _102316 A B) = (term185 _102289 _102316 A B).
Proof. exact (MK_COMB (@lem4069598 _102289 A) (@lem4069595 _102289 _102316 A B)). Qed.
Lemma lem4069602 {_102316 B : Type'} : (term178 _102316 B) = (term178 _102316 B).
Proof. exact (eq_refl (term178 _102316 B)). Qed.
Lemma lem4069603 {_102289 _102316 A B : Type'} : (term186 _102289 _102316 A B) = (term187 _102289 _102316 A B).
Proof. exact (MK_COMB (@lem4069602 _102316 B) (@lem4069599 _102289 _102316 A B)). Qed.
Lemma lem4069606 {_102289 B : Type'} : (term178 _102289 B) = (term178 _102289 B).
Proof. exact (eq_refl (term178 _102289 B)). Qed.
Lemma lem4069607 {_102289 _102316 A B : Type'} : (term188 _102289 _102316 A B) = (term189 _102289 _102316 A B).
Proof. exact (MK_COMB (@lem4069606 _102289 B) (@lem4069603 _102289 _102316 A B)). Qed.
Lemma lem4069610 {_102289 _102316 : Type'} : (term178 _102289 _102316) = (term178 _102289 _102316).
Proof. exact (eq_refl (term178 _102289 _102316)). Qed.
Lemma lem4069611 {_102289 _102316 A B : Type'} : (term190 _102289 _102316 A B) = (term191 _102289 _102316 A B).
Proof. exact (MK_COMB (@lem4069610 _102289 _102316) (@lem4069607 _102289 _102316 A B)). Qed.
Lemma lem4069614 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem4069615 {_102289 _102316 A B : Type'} : (term193 _102289 _102316 A B) = (term194 _102289 _102316 A B).
Proof. exact (MK_COMB (@lem4069614) (@lem4069611 _102289 _102316 A B)). Qed.
Lemma lem4069618 {B : Type'} : (term195 B) = (term195 B).
Proof. exact (eq_refl (term195 B)). Qed.
Lemma lem4069619 {_102289 _102316 A B : Type'} : (term196 _102289 _102316 A B) = (term197 _102289 _102316 A B).
Proof. exact (MK_COMB (@lem4069618 B) (@lem4069615 _102289 _102316 A B)). Qed.
Lemma lem4069622 {A B : Type'} : (term198 A B) = (term198 A B).
Proof. exact (eq_refl (term198 A B)). Qed.
Lemma lem4069623 {_102289 _102316 A B : Type'} : (term199 _102289 _102316 A B) = (term200 _102289 _102316 A B).
Proof. exact (MK_COMB (@lem4069622 A B) (@lem4069619 _102289 _102316 A B)). Qed.
Lemma lem4069626 {_102316 A : Type'} : (term201 _102316 A) = (term201 _102316 A).
Proof. exact (eq_refl (term201 _102316 A)). Qed.
Lemma lem4069627 {_102289 _102316 A B : Type'} : (term202 _102289 _102316 A B) = (term203 _102289 _102316 A B).
Proof. exact (MK_COMB (@lem4069626 _102316 A) (@lem4069623 _102289 _102316 A B)). Qed.
Lemma lem4069630 {_102289 A : Type'} : (term201 _102289 A) = (term201 _102289 A).
Proof. exact (eq_refl (term201 _102289 A)). Qed.
Lemma lem4069631 {_102289 _102316 A B : Type'} : (term204 _102289 _102316 A B) = (term205 _102289 _102316 A B).
Proof. exact (MK_COMB (@lem4069630 _102289 A) (@lem4069627 _102289 _102316 A B)). Qed.
Lemma lem4069634 {_102316 _87593 : Type'} : (term201 _102316 _87593) = (term201 _102316 _87593).
Proof. exact (eq_refl (term201 _102316 _87593)). Qed.
Lemma lem4069635 {_102289 _102316 _87593 A B : Type'} : (term206 _102289 _102316 _87593 A B) = (term207 _102289 _102316 _87593 A B).
Proof. exact (MK_COMB (@lem4069634 _102316 _87593) (@lem4069631 _102289 _102316 A B)). Qed.
Lemma lem4069638 {_102289 _87593 : Type'} : (term201 _102289 _87593) = (term201 _102289 _87593).
Proof. exact (eq_refl (term201 _102289 _87593)). Qed.
Lemma lem4069639 {_102289 _102316 _87593 A B : Type'} : (term208 _102289 _102316 _87593 A B) = (term209 _102289 _102316 _87593 A B).
Proof. exact (MK_COMB (@lem4069638 _102289 _87593) (@lem4069635 _102289 _102316 _87593 A B)). Qed.
Lemma lem4069642 {_102316 B : Type'} : (term198 _102316 B) = (term198 _102316 B).
Proof. exact (eq_refl (term198 _102316 B)). Qed.
Lemma lem4069643 {_102289 _102316 _87593 A B : Type'} : (term210 _102289 _102316 _87593 A B) = (term211 _102289 _102316 _87593 A B).
Proof. exact (MK_COMB (@lem4069642 _102316 B) (@lem4069639 _102289 _102316 _87593 A B)). Qed.
Lemma lem4069646 {_102316 _87604 : Type'} : (term198 _102316 _87604) = (term198 _102316 _87604).
Proof. exact (eq_refl (term198 _102316 _87604)). Qed.
Lemma lem4069647 {_102289 _102316 _87593 _87604 A B : Type'} : (term212 _102289 _102316 _87593 _87604 A B) = (term213 _102289 _102316 _87593 _87604 A B).
Proof. exact (MK_COMB (@lem4069646 _102316 _87604) (@lem4069643 _102289 _102316 _87593 A B)). Qed.
Lemma lem4069650 {_102289 B : Type'} : (term198 _102289 B) = (term198 _102289 B).
Proof. exact (eq_refl (term198 _102289 B)). Qed.
Lemma lem4069651 {_102289 _102316 _87593 _87604 A B : Type'} : (term214 _102289 _102316 _87593 _87604 A B) = (term215 _102289 _102316 _87593 _87604 A B).
Proof. exact (MK_COMB (@lem4069650 _102289 B) (@lem4069647 _102289 _102316 _87593 _87604 A B)). Qed.
Lemma lem4069654 {_102289 _87604 : Type'} : (term198 _102289 _87604) = (term198 _102289 _87604).
Proof. exact (eq_refl (term198 _102289 _87604)). Qed.
Lemma lem4069655 {_102289 _102316 _87593 _87604 A B : Type'} : (term216 _102289 _102316 _87593 _87604 A B) = (term217 _102289 _102316 _87593 _87604 A B).
Proof. exact (MK_COMB (@lem4069654 _102289 _87604) (@lem4069651 _102289 _102316 _87593 _87604 A B)). Qed.
Lemma lem4069658 {_102289 _102316 : Type'} : (term198 _102289 _102316) = (term198 _102289 _102316).
Proof. exact (eq_refl (term198 _102289 _102316)). Qed.
Lemma lem4069659 {_102289 _102316 _87593 _87604 A B : Type'} : (term218 _102289 _102316 _87593 _87604 A B) = (term219 _102289 _102316 _87593 _87604 A B).
Proof. exact (MK_COMB (@lem4069658 _102289 _102316) (@lem4069655 _102289 _102316 _87593 _87604 A B)). Qed.
Lemma lem4069662 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term220 _102289 _102316 n f s P) = (term220 _102289 _102316 n f s P).
Proof. exact (eq_refl (term220 _102289 _102316 n f s P)). Qed.
Lemma lem4069663 {_102289 _102316 _87593 _87604 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term159 _102289 _102316 _87593 _87604 A B n f s P) = (term221 _102289 _102316 _87593 _87604 A B n f s P).
Proof. exact (MK_COMB (@lem4069662 _102289 _102316 n f s P) (@lem4069659 _102289 _102316 _87593 _87604 A B)). Qed.
Lemma lem4069666 {_102289 _102316 _87593 _87604 A B : Type'} (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term222 _102289 _102316 _87593 _87604 A B f s P) = (term223 _102289 _102316 _87593 _87604 A B f s P).
Proof. exact (fun_ext (fun n : nat => @lem4069663 _102289 _102316 _87593 _87604 A B n f s P)). Qed.
Lemma lem4069667 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4069668 {_102289 _102316 _87593 _87604 A B : Type'} (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term224 _102289 _102316 _87593 _87604 A B f s P) = (term225 _102289 _102316 _87593 _87604 A B f s P).
Proof. exact (MK_COMB (@lem4069667) (@lem4069666 _102289 _102316 _87593 _87604 A B f s P)). Qed.
Lemma lem4069673 {_102289 _102316 _87593 _87604 A B : Type'} (s : _102289 -> Prop) (P : type686 _102316) : (term226 _102289 _102316 _87593 _87604 A B s P) = (term227 _102289 _102316 _87593 _87604 A B s P).
Proof. exact (fun_ext (fun f : _102289 -> _102316 => @lem4069668 _102289 _102316 _87593 _87604 A B f s P)). Qed.
Lemma lem4069674 {_102289 _102316 : Type'} : (@all (_102289 -> _102316)) = (@all (_102289 -> _102316)).
Proof. exact (eq_refl (@all (_102289 -> _102316))). Qed.
Lemma lem4069675 {_102289 _102316 _87593 _87604 A B : Type'} (s : _102289 -> Prop) (P : type686 _102316) : (term228 _102289 _102316 _87593 _87604 A B s P) = (term229 _102289 _102316 _87593 _87604 A B s P).
Proof. exact (MK_COMB (@lem4069674 _102289 _102316) (@lem4069673 _102289 _102316 _87593 _87604 A B s P)). Qed.
Lemma lem4069680 {_102289 _102316 _87593 _87604 A B : Type'} (P : type686 _102316) : (term230 _102289 _102316 _87593 _87604 A B P) = (term231 _102289 _102316 _87593 _87604 A B P).
Proof. exact (fun_ext (fun s : _102289 -> Prop => @lem4069675 _102289 _102316 _87593 _87604 A B s P)). Qed.
Lemma lem4069681 {_102289 : Type'} : (@all (_102289 -> Prop)) = (@all (_102289 -> Prop)).
Proof. exact (eq_refl (@all (_102289 -> Prop))). Qed.
Lemma lem4069682 {_102289 _102316 _87593 _87604 A B : Type'} (P : type686 _102316) : (term232 _102289 _102316 _87593 _87604 A B P) = (term233 _102289 _102316 _87593 _87604 A B P).
Proof. exact (MK_COMB (@lem4069681 _102289) (@lem4069680 _102289 _102316 _87593 _87604 A B P)). Qed.
Lemma lem4069687 {_102289 _102316 _87593 _87604 A B : Type'} : (term234 _102289 _102316 _87593 _87604 A B) = (term235 _102289 _102316 _87593 _87604 A B).
Proof. exact (fun_ext (fun P : type686 _102316 => @lem4069682 _102289 _102316 _87593 _87604 A B P)). Qed.
Lemma lem4069688 {_102316 : Type'} : (@all ((_102316 -> Prop) -> Prop)) = (@all ((_102316 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_102316 -> Prop) -> Prop))). Qed.
Lemma lem4069697 {_102289 _102316 _87593 _87604 A B : Type'} : (term236 _102289 _102316 _87593 _87604 A B) = (term237 _102289 _102316 _87593 _87604 A B).
Proof. exact (MK_COMB (@lem4069688 _102316) (@lem4069687 _102289 _102316 _87593 _87604 A B)). Qed.
Lemma lem4069702 {_102316 A : Type'} (f : A -> _102316) (s : A -> Prop) : (term238 _102316 A f s) = (term238 _102316 A f s).
Proof. exact (eq_refl (term238 _102316 A f s)). Qed.
Lemma lem4069703 {_102316 A : Type'} (f : A -> _102316) : (term239 _102316 A f) = (term239 _102316 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4069702 _102316 A f s)). Qed.
Lemma lem4069704 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4069705 {_102316 A : Type'} (f : A -> _102316) : (term240 _102316 A f) = (term240 _102316 A f).
Proof. exact (MK_COMB (@lem4069704 A) (@lem4069703 _102316 A f)). Qed.
Lemma lem4069706 {_102316 A : Type'} : (term241 _102316 A) = (term241 _102316 A).
Proof. exact (fun_ext (fun f : A -> _102316 => @lem4069705 _102316 A f)). Qed.
Lemma lem4069707 {_102316 A : Type'} : (@all (A -> _102316)) = (@all (A -> _102316)).
Proof. exact (eq_refl (@all (A -> _102316))). Qed.
Lemma lem4069708 {_102316 A : Type'} : (term152 _102316 A) = (term152 _102316 A).
Proof. exact (MK_COMB (@lem4069707 _102316 A) (@lem4069706 _102316 A)). Qed.
Lemma lem4069709 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4069710 {_102316 A : Type'} : (term164 _102316 A) = (term164 _102316 A).
Proof. exact (MK_COMB (@lem4069709) (@lem4069708 _102316 A)). Qed.
Lemma lem4069715 {_102289 A : Type'} (f : A -> _102289) (s : A -> Prop) : (term238 _102289 A f s) = (term238 _102289 A f s).
Proof. exact (eq_refl (term238 _102289 A f s)). Qed.
Lemma lem4069716 {_102289 A : Type'} (f : A -> _102289) : (term239 _102289 A f) = (term239 _102289 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4069715 _102289 A f s)). Qed.
Lemma lem4069717 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4069718 {_102289 A : Type'} (f : A -> _102289) : (term240 _102289 A f) = (term240 _102289 A f).
Proof. exact (MK_COMB (@lem4069717 A) (@lem4069716 _102289 A f)). Qed.
Lemma lem4069719 {_102289 A : Type'} : (term241 _102289 A) = (term241 _102289 A).
Proof. exact (fun_ext (fun f : A -> _102289 => @lem4069718 _102289 A f)). Qed.
Lemma lem4069720 {_102289 A : Type'} : (@all (A -> _102289)) = (@all (A -> _102289)).
Proof. exact (eq_refl (@all (A -> _102289))). Qed.
Lemma lem4069721 {_102289 A : Type'} : (term152 _102289 A) = (term152 _102289 A).
Proof. exact (MK_COMB (@lem4069720 _102289 A) (@lem4069719 _102289 A)). Qed.
Lemma lem4069722 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4069723 {_102289 A : Type'} : (term165 _102289 A) = (term165 _102289 A).
Proof. exact (MK_COMB (@lem4069722) (@lem4069721 _102289 A)). Qed.
Lemma lem4069724 {_102289 _102316 A : Type'} : (term167 _102289 _102316 A) = (term167 _102289 _102316 A).
Proof. exact (MK_COMB (@lem4069723 _102289 A) (@lem4069710 _102316 A)). Qed.
Lemma lem4069729 {_102316 B : Type'} (f : _102316 -> B) (s : _102316 -> Prop) : (term242 _102316 B f s) = (term242 _102316 B f s).
Proof. exact (eq_refl (term242 _102316 B f s)). Qed.
Lemma lem4069730 {_102316 B : Type'} (f : _102316 -> B) : (term243 _102316 B f) = (term243 _102316 B f).
Proof. exact (fun_ext (fun s : _102316 -> Prop => @lem4069729 _102316 B f s)). Qed.
Lemma lem4069731 {_102316 : Type'} : (@all (_102316 -> Prop)) = (@all (_102316 -> Prop)).
Proof. exact (eq_refl (@all (_102316 -> Prop))). Qed.
Lemma lem4069732 {_102316 B : Type'} (f : _102316 -> B) : (term244 _102316 B f) = (term244 _102316 B f).
Proof. exact (MK_COMB (@lem4069731 _102316) (@lem4069730 _102316 B f)). Qed.
Lemma lem4069733 {_102316 B : Type'} : (term245 _102316 B) = (term245 _102316 B).
Proof. exact (fun_ext (fun f : _102316 -> B => @lem4069732 _102316 B f)). Qed.
Lemma lem4069734 {_102316 B : Type'} : (@all (_102316 -> B)) = (@all (_102316 -> B)).
Proof. exact (eq_refl (@all (_102316 -> B))). Qed.
Lemma lem4069735 {_102316 B : Type'} : (term151 _102316 B) = (term151 _102316 B).
Proof. exact (MK_COMB (@lem4069734 _102316 B) (@lem4069733 _102316 B)). Qed.
Lemma lem4069736 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4069737 {_102316 B : Type'} : (term168 _102316 B) = (term168 _102316 B).
Proof. exact (MK_COMB (@lem4069736) (@lem4069735 _102316 B)). Qed.
Lemma lem4069738 {_102289 _102316 A B : Type'} : (term170 _102289 _102316 A B) = (term170 _102289 _102316 A B).
Proof. exact (MK_COMB (@lem4069737 _102316 B) (@lem4069724 _102289 _102316 A)). Qed.
Lemma lem4069743 {_102289 B : Type'} (f : _102289 -> B) (s : _102289 -> Prop) : (term242 _102289 B f s) = (term242 _102289 B f s).
Proof. exact (eq_refl (term242 _102289 B f s)). Qed.
Lemma lem4069744 {_102289 B : Type'} (f : _102289 -> B) : (term243 _102289 B f) = (term243 _102289 B f).
Proof. exact (fun_ext (fun s : _102289 -> Prop => @lem4069743 _102289 B f s)). Qed.
Lemma lem4069745 {_102289 : Type'} : (@all (_102289 -> Prop)) = (@all (_102289 -> Prop)).
Proof. exact (eq_refl (@all (_102289 -> Prop))). Qed.
Lemma lem4069746 {_102289 B : Type'} (f : _102289 -> B) : (term244 _102289 B f) = (term244 _102289 B f).
Proof. exact (MK_COMB (@lem4069745 _102289) (@lem4069744 _102289 B f)). Qed.
Lemma lem4069747 {_102289 B : Type'} : (term245 _102289 B) = (term245 _102289 B).
Proof. exact (fun_ext (fun f : _102289 -> B => @lem4069746 _102289 B f)). Qed.
Lemma lem4069748 {_102289 B : Type'} : (@all (_102289 -> B)) = (@all (_102289 -> B)).
Proof. exact (eq_refl (@all (_102289 -> B))). Qed.
Lemma lem4069749 {_102289 B : Type'} : (term151 _102289 B) = (term151 _102289 B).
Proof. exact (MK_COMB (@lem4069748 _102289 B) (@lem4069747 _102289 B)). Qed.
Lemma lem4069750 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4069751 {_102289 B : Type'} : (term168 _102289 B) = (term168 _102289 B).
Proof. exact (MK_COMB (@lem4069750) (@lem4069749 _102289 B)). Qed.
Lemma lem4069752 {_102289 _102316 A B : Type'} : (term172 _102289 _102316 A B) = (term172 _102289 _102316 A B).
Proof. exact (MK_COMB (@lem4069751 _102289 B) (@lem4069738 _102289 _102316 A B)). Qed.
Lemma lem4069757 {_102289 _102316 : Type'} (f : _102289 -> _102316) (s : _102289 -> Prop) : (term242 _102289 _102316 f s) = (term242 _102289 _102316 f s).
Proof. exact (eq_refl (term242 _102289 _102316 f s)). Qed.
Lemma lem4069758 {_102289 _102316 : Type'} (f : _102289 -> _102316) : (term243 _102289 _102316 f) = (term243 _102289 _102316 f).
Proof. exact (fun_ext (fun s : _102289 -> Prop => @lem4069757 _102289 _102316 f s)). Qed.
Lemma lem4069759 {_102289 : Type'} : (@all (_102289 -> Prop)) = (@all (_102289 -> Prop)).
Proof. exact (eq_refl (@all (_102289 -> Prop))). Qed.
Lemma lem4069760 {_102289 _102316 : Type'} (f : _102289 -> _102316) : (term244 _102289 _102316 f) = (term244 _102289 _102316 f).
Proof. exact (MK_COMB (@lem4069759 _102289) (@lem4069758 _102289 _102316 f)). Qed.
Lemma lem4069761 {_102289 _102316 : Type'} : (term245 _102289 _102316) = (term245 _102289 _102316).
Proof. exact (fun_ext (fun f : _102289 -> _102316 => @lem4069760 _102289 _102316 f)). Qed.
Lemma lem4069762 {_102289 _102316 : Type'} : (@all (_102289 -> _102316)) = (@all (_102289 -> _102316)).
Proof. exact (eq_refl (@all (_102289 -> _102316))). Qed.
Lemma lem4069763 {_102289 _102316 : Type'} : (term151 _102289 _102316) = (term151 _102289 _102316).
Proof. exact (MK_COMB (@lem4069762 _102289 _102316) (@lem4069761 _102289 _102316)). Qed.
Lemma lem4069764 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4069765 {_102289 _102316 : Type'} : (term168 _102289 _102316) = (term168 _102289 _102316).
Proof. exact (MK_COMB (@lem4069764) (@lem4069763 _102289 _102316)). Qed.
Lemma lem4069766 {_102289 _102316 A B : Type'} : (term174 _102289 _102316 A B) = (term174 _102289 _102316 A B).
Proof. exact (MK_COMB (@lem4069765 _102289 _102316) (@lem4069752 _102289 _102316 A B)). Qed.
Lemma lem4069771 {B : Type'} (f : B -> B) (s : B -> Prop) : (term246 B f s) = (term246 B f s).
Proof. exact (eq_refl (term246 B f s)). Qed.
Lemma lem4069772 {B : Type'} (f : B -> B) : (term247 B f) = (term247 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4069771 B f s)). Qed.
Lemma lem4069773 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4069774 {B : Type'} (f : B -> B) : (term248 B f) = (term248 B f).
Proof. exact (MK_COMB (@lem4069773 B) (@lem4069772 B f)). Qed.
Lemma lem4069775 {B : Type'} : (term249 B) = (term249 B).
Proof. exact (fun_ext (fun f : B -> B => @lem4069774 B f)). Qed.
Lemma lem4069776 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem4069777 {B : Type'} : (term154 B) = (term154 B).
Proof. exact (MK_COMB (@lem4069776 B) (@lem4069775 B)). Qed.
Lemma lem4069778 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4069779 {B : Type'} : (term175 B) = (term175 B).
Proof. exact (MK_COMB (@lem4069778) (@lem4069777 B)). Qed.
Lemma lem4069780 {_102289 _102316 A B : Type'} : (term177 _102289 _102316 A B) = (term177 _102289 _102316 A B).
Proof. exact (MK_COMB (@lem4069779 B) (@lem4069766 _102289 _102316 A B)). Qed.
Lemma lem4069785 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term250 A B f s) = (term250 A B f s).
Proof. exact (eq_refl (term250 A B f s)). Qed.
Lemma lem4069786 {A B : Type'} (f : A -> B) : (term251 A B f) = (term251 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4069785 A B f s)). Qed.
Lemma lem4069787 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4069788 {A B : Type'} (f : A -> B) : (term252 A B f) = (term252 A B f).
Proof. exact (MK_COMB (@lem4069787 A) (@lem4069786 A B f)). Qed.
Lemma lem4069789 {A B : Type'} : (term253 A B) = (term253 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4069788 A B f)). Qed.
Lemma lem4069790 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4069791 {A B : Type'} : (term153 A B) = (term153 A B).
Proof. exact (MK_COMB (@lem4069790 A B) (@lem4069789 A B)). Qed.
Lemma lem4069792 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4069793 {A B : Type'} : (term178 A B) = (term178 A B).
Proof. exact (MK_COMB (@lem4069792) (@lem4069791 A B)). Qed.
Lemma lem4069794 {_102289 _102316 A B : Type'} : (term180 _102289 _102316 A B) = (term180 _102289 _102316 A B).
Proof. exact (MK_COMB (@lem4069793 A B) (@lem4069780 _102289 _102316 A B)). Qed.
Lemma lem4069799 {_102316 A : Type'} (f : A -> _102316) (s : A -> Prop) : (term254 _102316 A f s) = (term254 _102316 A f s).
Proof. exact (eq_refl (term254 _102316 A f s)). Qed.
Lemma lem4069800 {_102316 A : Type'} (f : A -> _102316) : (term255 _102316 A f) = (term255 _102316 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4069799 _102316 A f s)). Qed.
Lemma lem4069801 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4069802 {_102316 A : Type'} (f : A -> _102316) : (term256 _102316 A f) = (term256 _102316 A f).
Proof. exact (MK_COMB (@lem4069801 A) (@lem4069800 _102316 A f)). Qed.
Lemma lem4069803 {_102316 A : Type'} : (term257 _102316 A) = (term257 _102316 A).
Proof. exact (fun_ext (fun f : A -> _102316 => @lem4069802 _102316 A f)). Qed.
Lemma lem4069804 {_102316 A : Type'} : (@all (A -> _102316)) = (@all (A -> _102316)).
Proof. exact (eq_refl (@all (A -> _102316))). Qed.
Lemma lem4069805 {_102316 A : Type'} : (term155 _102316 A) = (term155 _102316 A).
Proof. exact (MK_COMB (@lem4069804 _102316 A) (@lem4069803 _102316 A)). Qed.
Lemma lem4069806 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4069807 {_102316 A : Type'} : (term181 _102316 A) = (term181 _102316 A).
Proof. exact (MK_COMB (@lem4069806) (@lem4069805 _102316 A)). Qed.
Lemma lem4069808 {_102289 _102316 A B : Type'} : (term183 _102289 _102316 A B) = (term183 _102289 _102316 A B).
Proof. exact (MK_COMB (@lem4069807 _102316 A) (@lem4069794 _102289 _102316 A B)). Qed.
Lemma lem4069813 {_102289 A : Type'} (f : A -> _102289) (s : A -> Prop) : (term254 _102289 A f s) = (term254 _102289 A f s).
Proof. exact (eq_refl (term254 _102289 A f s)). Qed.
Lemma lem4069814 {_102289 A : Type'} (f : A -> _102289) : (term255 _102289 A f) = (term255 _102289 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4069813 _102289 A f s)). Qed.
Lemma lem4069815 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4069816 {_102289 A : Type'} (f : A -> _102289) : (term256 _102289 A f) = (term256 _102289 A f).
Proof. exact (MK_COMB (@lem4069815 A) (@lem4069814 _102289 A f)). Qed.
Lemma lem4069817 {_102289 A : Type'} : (term257 _102289 A) = (term257 _102289 A).
Proof. exact (fun_ext (fun f : A -> _102289 => @lem4069816 _102289 A f)). Qed.
Lemma lem4069818 {_102289 A : Type'} : (@all (A -> _102289)) = (@all (A -> _102289)).
Proof. exact (eq_refl (@all (A -> _102289))). Qed.
Lemma lem4069819 {_102289 A : Type'} : (term155 _102289 A) = (term155 _102289 A).
Proof. exact (MK_COMB (@lem4069818 _102289 A) (@lem4069817 _102289 A)). Qed.
Lemma lem4069820 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4069821 {_102289 A : Type'} : (term181 _102289 A) = (term181 _102289 A).
Proof. exact (MK_COMB (@lem4069820) (@lem4069819 _102289 A)). Qed.
Lemma lem4069822 {_102289 _102316 A B : Type'} : (term185 _102289 _102316 A B) = (term185 _102289 _102316 A B).
Proof. exact (MK_COMB (@lem4069821 _102289 A) (@lem4069808 _102289 _102316 A B)). Qed.
Lemma lem4069827 {_102316 B : Type'} (f : _102316 -> B) (s : _102316 -> Prop) : (term250 _102316 B f s) = (term250 _102316 B f s).
Proof. exact (eq_refl (term250 _102316 B f s)). Qed.
Lemma lem4069828 {_102316 B : Type'} (f : _102316 -> B) : (term251 _102316 B f) = (term251 _102316 B f).
Proof. exact (fun_ext (fun s : _102316 -> Prop => @lem4069827 _102316 B f s)). Qed.
Lemma lem4069829 {_102316 : Type'} : (@all (_102316 -> Prop)) = (@all (_102316 -> Prop)).
Proof. exact (eq_refl (@all (_102316 -> Prop))). Qed.
Lemma lem4069830 {_102316 B : Type'} (f : _102316 -> B) : (term252 _102316 B f) = (term252 _102316 B f).
Proof. exact (MK_COMB (@lem4069829 _102316) (@lem4069828 _102316 B f)). Qed.
Lemma lem4069831 {_102316 B : Type'} : (term253 _102316 B) = (term253 _102316 B).
Proof. exact (fun_ext (fun f : _102316 -> B => @lem4069830 _102316 B f)). Qed.
Lemma lem4069832 {_102316 B : Type'} : (@all (_102316 -> B)) = (@all (_102316 -> B)).
Proof. exact (eq_refl (@all (_102316 -> B))). Qed.
Lemma lem4069833 {_102316 B : Type'} : (term153 _102316 B) = (term153 _102316 B).
Proof. exact (MK_COMB (@lem4069832 _102316 B) (@lem4069831 _102316 B)). Qed.
Lemma lem4069834 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4069835 {_102316 B : Type'} : (term178 _102316 B) = (term178 _102316 B).
Proof. exact (MK_COMB (@lem4069834) (@lem4069833 _102316 B)). Qed.
Lemma lem4069836 {_102289 _102316 A B : Type'} : (term187 _102289 _102316 A B) = (term187 _102289 _102316 A B).
Proof. exact (MK_COMB (@lem4069835 _102316 B) (@lem4069822 _102289 _102316 A B)). Qed.
Lemma lem4069841 {_102289 B : Type'} (f : _102289 -> B) (s : _102289 -> Prop) : (term250 _102289 B f s) = (term250 _102289 B f s).
Proof. exact (eq_refl (term250 _102289 B f s)). Qed.
Lemma lem4069842 {_102289 B : Type'} (f : _102289 -> B) : (term251 _102289 B f) = (term251 _102289 B f).
Proof. exact (fun_ext (fun s : _102289 -> Prop => @lem4069841 _102289 B f s)). Qed.
Lemma lem4069843 {_102289 : Type'} : (@all (_102289 -> Prop)) = (@all (_102289 -> Prop)).
Proof. exact (eq_refl (@all (_102289 -> Prop))). Qed.
Lemma lem4069844 {_102289 B : Type'} (f : _102289 -> B) : (term252 _102289 B f) = (term252 _102289 B f).
Proof. exact (MK_COMB (@lem4069843 _102289) (@lem4069842 _102289 B f)). Qed.
Lemma lem4069845 {_102289 B : Type'} : (term253 _102289 B) = (term253 _102289 B).
Proof. exact (fun_ext (fun f : _102289 -> B => @lem4069844 _102289 B f)). Qed.
Lemma lem4069846 {_102289 B : Type'} : (@all (_102289 -> B)) = (@all (_102289 -> B)).
Proof. exact (eq_refl (@all (_102289 -> B))). Qed.
Lemma lem4069847 {_102289 B : Type'} : (term153 _102289 B) = (term153 _102289 B).
Proof. exact (MK_COMB (@lem4069846 _102289 B) (@lem4069845 _102289 B)). Qed.
Lemma lem4069848 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4069849 {_102289 B : Type'} : (term178 _102289 B) = (term178 _102289 B).
Proof. exact (MK_COMB (@lem4069848) (@lem4069847 _102289 B)). Qed.
Lemma lem4069850 {_102289 _102316 A B : Type'} : (term189 _102289 _102316 A B) = (term189 _102289 _102316 A B).
Proof. exact (MK_COMB (@lem4069849 _102289 B) (@lem4069836 _102289 _102316 A B)). Qed.
Lemma lem4069855 {_102289 _102316 : Type'} (f : _102289 -> _102316) (s : _102289 -> Prop) : (term250 _102289 _102316 f s) = (term250 _102289 _102316 f s).
Proof. exact (eq_refl (term250 _102289 _102316 f s)). Qed.
Lemma lem4069856 {_102289 _102316 : Type'} (f : _102289 -> _102316) : (term251 _102289 _102316 f) = (term251 _102289 _102316 f).
Proof. exact (fun_ext (fun s : _102289 -> Prop => @lem4069855 _102289 _102316 f s)). Qed.
Lemma lem4069857 {_102289 : Type'} : (@all (_102289 -> Prop)) = (@all (_102289 -> Prop)).
Proof. exact (eq_refl (@all (_102289 -> Prop))). Qed.
Lemma lem4069858 {_102289 _102316 : Type'} (f : _102289 -> _102316) : (term252 _102289 _102316 f) = (term252 _102289 _102316 f).
Proof. exact (MK_COMB (@lem4069857 _102289) (@lem4069856 _102289 _102316 f)). Qed.
Lemma lem4069859 {_102289 _102316 : Type'} : (term253 _102289 _102316) = (term253 _102289 _102316).
Proof. exact (fun_ext (fun f : _102289 -> _102316 => @lem4069858 _102289 _102316 f)). Qed.
Lemma lem4069860 {_102289 _102316 : Type'} : (@all (_102289 -> _102316)) = (@all (_102289 -> _102316)).
Proof. exact (eq_refl (@all (_102289 -> _102316))). Qed.
Lemma lem4069861 {_102289 _102316 : Type'} : (term153 _102289 _102316) = (term153 _102289 _102316).
Proof. exact (MK_COMB (@lem4069860 _102289 _102316) (@lem4069859 _102289 _102316)). Qed.
Lemma lem4069862 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4069863 {_102289 _102316 : Type'} : (term178 _102289 _102316) = (term178 _102289 _102316).
Proof. exact (MK_COMB (@lem4069862) (@lem4069861 _102289 _102316)). Qed.
Lemma lem4069864 {_102289 _102316 A B : Type'} : (term191 _102289 _102316 A B) = (term191 _102289 _102316 A B).
Proof. exact (MK_COMB (@lem4069863 _102289 _102316) (@lem4069850 _102289 _102316 A B)). Qed.
Lemma lem4069873 (n : nat) (m : nat) (p : nat) : (term258 n m p) = (term258 n m p).
Proof. exact (eq_refl (term258 n m p)). Qed.
Lemma lem4069874 (n : nat) (m : nat) : (term259 n m) = (term259 n m).
Proof. exact (fun_ext (fun p : nat => @lem4069873 n m p)). Qed.
Lemma lem4069875 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4069876 (n : nat) (m : nat) : (term260 n m) = (term260 n m).
Proof. exact (MK_COMB (@lem4069875) (@lem4069874 n m)). Qed.
Lemma lem4069877 (m : nat) : (term261 m) = (term261 m).
Proof. exact (fun_ext (fun n : nat => @lem4069876 n m)). Qed.
Lemma lem4069878 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4069879 (m : nat) : (term262 m) = (term262 m).
Proof. exact (MK_COMB (@lem4069878) (@lem4069877 m)). Qed.
Lemma lem4069880 : term263 = term263.
Proof. exact (fun_ext (fun m : nat => @lem4069879 m)). Qed.
Lemma lem4069881 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4069882 : term264 = term264.
Proof. exact (MK_COMB (@lem4069881) (@lem4069880)). Qed.
Lemma lem4069883 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4069884 : term192 = term192.
Proof. exact (MK_COMB (@lem4069883) (@lem4069882)). Qed.
Lemma lem4069885 {_102289 _102316 A B : Type'} : (term194 _102289 _102316 A B) = (term194 _102289 _102316 A B).
Proof. exact (MK_COMB (@lem4069884) (@lem4069864 _102289 _102316 A B)). Qed.
Lemma lem4069890 {B : Type'} (s : B -> Prop) (f : B -> B) (t : B -> Prop) : (term265 B s f t) = (term265 B s f t).
Proof. exact (eq_refl (term265 B s f t)). Qed.
Lemma lem4069891 {B : Type'} (s : B -> Prop) (f : B -> B) : (term266 B s f) = (term266 B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4069890 B s f t)). Qed.
Lemma lem4069892 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4069893 {B : Type'} (s : B -> Prop) (f : B -> B) : (term267 B s f) = (term267 B s f).
Proof. exact (MK_COMB (@lem4069892 B) (@lem4069891 B s f)). Qed.
Lemma lem4069894 {B : Type'} (f : B -> B) : (term268 B f) = (term268 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4069893 B s f)). Qed.
Lemma lem4069895 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4069896 {B : Type'} (f : B -> B) : (term269 B f) = (term269 B f).
Proof. exact (MK_COMB (@lem4069895 B) (@lem4069894 B f)). Qed.
Lemma lem4069897 {B : Type'} : (term270 B) = (term270 B).
Proof. exact (fun_ext (fun f : B -> B => @lem4069896 B f)). Qed.
Lemma lem4069898 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem4069899 {B : Type'} : (term158 B) = (term158 B).
Proof. exact (MK_COMB (@lem4069898 B) (@lem4069897 B)). Qed.
Lemma lem4069900 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4069901 {B : Type'} : (term195 B) = (term195 B).
Proof. exact (MK_COMB (@lem4069900) (@lem4069899 B)). Qed.
Lemma lem4069902 {_102289 _102316 A B : Type'} : (term197 _102289 _102316 A B) = (term197 _102289 _102316 A B).
Proof. exact (MK_COMB (@lem4069901 B) (@lem4069885 _102289 _102316 A B)). Qed.
Lemma lem4069907 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term271 A B s f t) = (term271 A B s f t).
Proof. exact (eq_refl (term271 A B s f t)). Qed.
Lemma lem4069908 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term272 A B s f) = (term272 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4069907 A B s f t)). Qed.
Lemma lem4069909 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4069910 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term273 A B s f) = (term273 A B s f).
Proof. exact (MK_COMB (@lem4069909 A) (@lem4069908 A B s f)). Qed.
Lemma lem4069911 {A B : Type'} (f : A -> B) : (term274 A B f) = (term274 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4069910 A B s f)). Qed.
Lemma lem4069912 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4069913 {A B : Type'} (f : A -> B) : (term275 A B f) = (term275 A B f).
Proof. exact (MK_COMB (@lem4069912 A) (@lem4069911 A B f)). Qed.
Lemma lem4069914 {A B : Type'} : (term276 A B) = (term276 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4069913 A B f)). Qed.
Lemma lem4069915 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4069916 {A B : Type'} : (term156 A B) = (term156 A B).
Proof. exact (MK_COMB (@lem4069915 A B) (@lem4069914 A B)). Qed.
Lemma lem4069917 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4069918 {A B : Type'} : (term198 A B) = (term198 A B).
Proof. exact (MK_COMB (@lem4069917) (@lem4069916 A B)). Qed.
Lemma lem4069919 {_102289 _102316 A B : Type'} : (term200 _102289 _102316 A B) = (term200 _102289 _102316 A B).
Proof. exact (MK_COMB (@lem4069918 A B) (@lem4069902 _102289 _102316 A B)). Qed.
Lemma lem4069924 {_102316 A : Type'} (s : A -> Prop) (f : A -> _102316) (t : A -> Prop) : (term277 _102316 A s f t) = (term277 _102316 A s f t).
Proof. exact (eq_refl (term277 _102316 A s f t)). Qed.
Lemma lem4069925 {_102316 A : Type'} (s : A -> Prop) (f : A -> _102316) : (term278 _102316 A s f) = (term278 _102316 A s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4069924 _102316 A s f t)). Qed.
Lemma lem4069926 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4069927 {_102316 A : Type'} (s : A -> Prop) (f : A -> _102316) : (term279 _102316 A s f) = (term279 _102316 A s f).
Proof. exact (MK_COMB (@lem4069926 A) (@lem4069925 _102316 A s f)). Qed.
Lemma lem4069928 {_102316 A : Type'} (f : A -> _102316) : (term280 _102316 A f) = (term280 _102316 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4069927 _102316 A s f)). Qed.
Lemma lem4069929 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4069930 {_102316 A : Type'} (f : A -> _102316) : (term281 _102316 A f) = (term281 _102316 A f).
Proof. exact (MK_COMB (@lem4069929 A) (@lem4069928 _102316 A f)). Qed.
Lemma lem4069931 {_102316 A : Type'} : (term282 _102316 A) = (term282 _102316 A).
Proof. exact (fun_ext (fun f : A -> _102316 => @lem4069930 _102316 A f)). Qed.
Lemma lem4069932 {_102316 A : Type'} : (@all (A -> _102316)) = (@all (A -> _102316)).
Proof. exact (eq_refl (@all (A -> _102316))). Qed.
Lemma lem4069933 {_102316 A : Type'} : (term157 _102316 A) = (term157 _102316 A).
Proof. exact (MK_COMB (@lem4069932 _102316 A) (@lem4069931 _102316 A)). Qed.
Lemma lem4069934 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4069935 {_102316 A : Type'} : (term201 _102316 A) = (term201 _102316 A).
Proof. exact (MK_COMB (@lem4069934) (@lem4069933 _102316 A)). Qed.
Lemma lem4069936 {_102289 _102316 A B : Type'} : (term203 _102289 _102316 A B) = (term203 _102289 _102316 A B).
Proof. exact (MK_COMB (@lem4069935 _102316 A) (@lem4069919 _102289 _102316 A B)). Qed.
Lemma lem4069941 {_102289 A : Type'} (s : A -> Prop) (f : A -> _102289) (t : A -> Prop) : (term277 _102289 A s f t) = (term277 _102289 A s f t).
Proof. exact (eq_refl (term277 _102289 A s f t)). Qed.
Lemma lem4069942 {_102289 A : Type'} (s : A -> Prop) (f : A -> _102289) : (term278 _102289 A s f) = (term278 _102289 A s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4069941 _102289 A s f t)). Qed.
Lemma lem4069943 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4069944 {_102289 A : Type'} (s : A -> Prop) (f : A -> _102289) : (term279 _102289 A s f) = (term279 _102289 A s f).
Proof. exact (MK_COMB (@lem4069943 A) (@lem4069942 _102289 A s f)). Qed.
Lemma lem4069945 {_102289 A : Type'} (f : A -> _102289) : (term280 _102289 A f) = (term280 _102289 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4069944 _102289 A s f)). Qed.
Lemma lem4069946 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4069947 {_102289 A : Type'} (f : A -> _102289) : (term281 _102289 A f) = (term281 _102289 A f).
Proof. exact (MK_COMB (@lem4069946 A) (@lem4069945 _102289 A f)). Qed.
Lemma lem4069948 {_102289 A : Type'} : (term282 _102289 A) = (term282 _102289 A).
Proof. exact (fun_ext (fun f : A -> _102289 => @lem4069947 _102289 A f)). Qed.
Lemma lem4069949 {_102289 A : Type'} : (@all (A -> _102289)) = (@all (A -> _102289)).
Proof. exact (eq_refl (@all (A -> _102289))). Qed.
Lemma lem4069950 {_102289 A : Type'} : (term157 _102289 A) = (term157 _102289 A).
Proof. exact (MK_COMB (@lem4069949 _102289 A) (@lem4069948 _102289 A)). Qed.
Lemma lem4069951 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4069952 {_102289 A : Type'} : (term201 _102289 A) = (term201 _102289 A).
Proof. exact (MK_COMB (@lem4069951) (@lem4069950 _102289 A)). Qed.
Lemma lem4069953 {_102289 _102316 A B : Type'} : (term205 _102289 _102316 A B) = (term205 _102289 _102316 A B).
Proof. exact (MK_COMB (@lem4069952 _102289 A) (@lem4069936 _102289 _102316 A B)). Qed.
Lemma lem4069958 {_102316 _87593 : Type'} (s : _87593 -> Prop) (f : _87593 -> _102316) (t : _87593 -> Prop) : (term277 _102316 _87593 s f t) = (term277 _102316 _87593 s f t).
Proof. exact (eq_refl (term277 _102316 _87593 s f t)). Qed.
Lemma lem4069959 {_102316 _87593 : Type'} (s : _87593 -> Prop) (f : _87593 -> _102316) : (term278 _102316 _87593 s f) = (term278 _102316 _87593 s f).
Proof. exact (fun_ext (fun t : _87593 -> Prop => @lem4069958 _102316 _87593 s f t)). Qed.
Lemma lem4069960 {_87593 : Type'} : (@all (_87593 -> Prop)) = (@all (_87593 -> Prop)).
Proof. exact (eq_refl (@all (_87593 -> Prop))). Qed.
Lemma lem4069961 {_102316 _87593 : Type'} (s : _87593 -> Prop) (f : _87593 -> _102316) : (term279 _102316 _87593 s f) = (term279 _102316 _87593 s f).
Proof. exact (MK_COMB (@lem4069960 _87593) (@lem4069959 _102316 _87593 s f)). Qed.
Lemma lem4069962 {_102316 _87593 : Type'} (f : _87593 -> _102316) : (term280 _102316 _87593 f) = (term280 _102316 _87593 f).
Proof. exact (fun_ext (fun s : _87593 -> Prop => @lem4069961 _102316 _87593 s f)). Qed.
Lemma lem4069963 {_87593 : Type'} : (@all (_87593 -> Prop)) = (@all (_87593 -> Prop)).
Proof. exact (eq_refl (@all (_87593 -> Prop))). Qed.
Lemma lem4069964 {_102316 _87593 : Type'} (f : _87593 -> _102316) : (term281 _102316 _87593 f) = (term281 _102316 _87593 f).
Proof. exact (MK_COMB (@lem4069963 _87593) (@lem4069962 _102316 _87593 f)). Qed.
Lemma lem4069965 {_102316 _87593 : Type'} : (term282 _102316 _87593) = (term282 _102316 _87593).
Proof. exact (fun_ext (fun f : _87593 -> _102316 => @lem4069964 _102316 _87593 f)). Qed.
Lemma lem4069966 {_102316 _87593 : Type'} : (@all (_87593 -> _102316)) = (@all (_87593 -> _102316)).
Proof. exact (eq_refl (@all (_87593 -> _102316))). Qed.
Lemma lem4069967 {_102316 _87593 : Type'} : (term157 _102316 _87593) = (term157 _102316 _87593).
Proof. exact (MK_COMB (@lem4069966 _102316 _87593) (@lem4069965 _102316 _87593)). Qed.
Lemma lem4069968 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4069969 {_102316 _87593 : Type'} : (term201 _102316 _87593) = (term201 _102316 _87593).
Proof. exact (MK_COMB (@lem4069968) (@lem4069967 _102316 _87593)). Qed.
Lemma lem4069970 {_102289 _102316 _87593 A B : Type'} : (term207 _102289 _102316 _87593 A B) = (term207 _102289 _102316 _87593 A B).
Proof. exact (MK_COMB (@lem4069969 _102316 _87593) (@lem4069953 _102289 _102316 A B)). Qed.
Lemma lem4069975 {_102289 _87593 : Type'} (s : _87593 -> Prop) (f : _87593 -> _102289) (t : _87593 -> Prop) : (term277 _102289 _87593 s f t) = (term277 _102289 _87593 s f t).
Proof. exact (eq_refl (term277 _102289 _87593 s f t)). Qed.
Lemma lem4069976 {_102289 _87593 : Type'} (s : _87593 -> Prop) (f : _87593 -> _102289) : (term278 _102289 _87593 s f) = (term278 _102289 _87593 s f).
Proof. exact (fun_ext (fun t : _87593 -> Prop => @lem4069975 _102289 _87593 s f t)). Qed.
Lemma lem4069977 {_87593 : Type'} : (@all (_87593 -> Prop)) = (@all (_87593 -> Prop)).
Proof. exact (eq_refl (@all (_87593 -> Prop))). Qed.
Lemma lem4069978 {_102289 _87593 : Type'} (s : _87593 -> Prop) (f : _87593 -> _102289) : (term279 _102289 _87593 s f) = (term279 _102289 _87593 s f).
Proof. exact (MK_COMB (@lem4069977 _87593) (@lem4069976 _102289 _87593 s f)). Qed.
Lemma lem4069979 {_102289 _87593 : Type'} (f : _87593 -> _102289) : (term280 _102289 _87593 f) = (term280 _102289 _87593 f).
Proof. exact (fun_ext (fun s : _87593 -> Prop => @lem4069978 _102289 _87593 s f)). Qed.
Lemma lem4069980 {_87593 : Type'} : (@all (_87593 -> Prop)) = (@all (_87593 -> Prop)).
Proof. exact (eq_refl (@all (_87593 -> Prop))). Qed.
Lemma lem4069981 {_102289 _87593 : Type'} (f : _87593 -> _102289) : (term281 _102289 _87593 f) = (term281 _102289 _87593 f).
Proof. exact (MK_COMB (@lem4069980 _87593) (@lem4069979 _102289 _87593 f)). Qed.
Lemma lem4069982 {_102289 _87593 : Type'} : (term282 _102289 _87593) = (term282 _102289 _87593).
Proof. exact (fun_ext (fun f : _87593 -> _102289 => @lem4069981 _102289 _87593 f)). Qed.
Lemma lem4069983 {_102289 _87593 : Type'} : (@all (_87593 -> _102289)) = (@all (_87593 -> _102289)).
Proof. exact (eq_refl (@all (_87593 -> _102289))). Qed.
Lemma lem4069984 {_102289 _87593 : Type'} : (term157 _102289 _87593) = (term157 _102289 _87593).
Proof. exact (MK_COMB (@lem4069983 _102289 _87593) (@lem4069982 _102289 _87593)). Qed.
Lemma lem4069985 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4069986 {_102289 _87593 : Type'} : (term201 _102289 _87593) = (term201 _102289 _87593).
Proof. exact (MK_COMB (@lem4069985) (@lem4069984 _102289 _87593)). Qed.
Lemma lem4069987 {_102289 _102316 _87593 A B : Type'} : (term209 _102289 _102316 _87593 A B) = (term209 _102289 _102316 _87593 A B).
Proof. exact (MK_COMB (@lem4069986 _102289 _87593) (@lem4069970 _102289 _102316 _87593 A B)). Qed.
Lemma lem4069992 {_102316 B : Type'} (s : _102316 -> Prop) (f : _102316 -> B) (t : _102316 -> Prop) : (term271 _102316 B s f t) = (term271 _102316 B s f t).
Proof. exact (eq_refl (term271 _102316 B s f t)). Qed.
Lemma lem4069993 {_102316 B : Type'} (s : _102316 -> Prop) (f : _102316 -> B) : (term272 _102316 B s f) = (term272 _102316 B s f).
Proof. exact (fun_ext (fun t : _102316 -> Prop => @lem4069992 _102316 B s f t)). Qed.
Lemma lem4069994 {_102316 : Type'} : (@all (_102316 -> Prop)) = (@all (_102316 -> Prop)).
Proof. exact (eq_refl (@all (_102316 -> Prop))). Qed.
Lemma lem4069995 {_102316 B : Type'} (s : _102316 -> Prop) (f : _102316 -> B) : (term273 _102316 B s f) = (term273 _102316 B s f).
Proof. exact (MK_COMB (@lem4069994 _102316) (@lem4069993 _102316 B s f)). Qed.
Lemma lem4069996 {_102316 B : Type'} (f : _102316 -> B) : (term274 _102316 B f) = (term274 _102316 B f).
Proof. exact (fun_ext (fun s : _102316 -> Prop => @lem4069995 _102316 B s f)). Qed.
Lemma lem4069997 {_102316 : Type'} : (@all (_102316 -> Prop)) = (@all (_102316 -> Prop)).
Proof. exact (eq_refl (@all (_102316 -> Prop))). Qed.
Lemma lem4069998 {_102316 B : Type'} (f : _102316 -> B) : (term275 _102316 B f) = (term275 _102316 B f).
Proof. exact (MK_COMB (@lem4069997 _102316) (@lem4069996 _102316 B f)). Qed.
Lemma lem4069999 {_102316 B : Type'} : (term276 _102316 B) = (term276 _102316 B).
Proof. exact (fun_ext (fun f : _102316 -> B => @lem4069998 _102316 B f)). Qed.
Lemma lem4070000 {_102316 B : Type'} : (@all (_102316 -> B)) = (@all (_102316 -> B)).
Proof. exact (eq_refl (@all (_102316 -> B))). Qed.
Lemma lem4070001 {_102316 B : Type'} : (term156 _102316 B) = (term156 _102316 B).
Proof. exact (MK_COMB (@lem4070000 _102316 B) (@lem4069999 _102316 B)). Qed.
Lemma lem4070002 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4070003 {_102316 B : Type'} : (term198 _102316 B) = (term198 _102316 B).
Proof. exact (MK_COMB (@lem4070002) (@lem4070001 _102316 B)). Qed.
Lemma lem4070004 {_102289 _102316 _87593 A B : Type'} : (term211 _102289 _102316 _87593 A B) = (term211 _102289 _102316 _87593 A B).
Proof. exact (MK_COMB (@lem4070003 _102316 B) (@lem4069987 _102289 _102316 _87593 A B)). Qed.
Lemma lem4070009 {_102316 _87604 : Type'} (s : _102316 -> Prop) (f : _102316 -> _87604) (t : _102316 -> Prop) : (term271 _102316 _87604 s f t) = (term271 _102316 _87604 s f t).
Proof. exact (eq_refl (term271 _102316 _87604 s f t)). Qed.
Lemma lem4070010 {_102316 _87604 : Type'} (s : _102316 -> Prop) (f : _102316 -> _87604) : (term272 _102316 _87604 s f) = (term272 _102316 _87604 s f).
Proof. exact (fun_ext (fun t : _102316 -> Prop => @lem4070009 _102316 _87604 s f t)). Qed.
Lemma lem4070011 {_102316 : Type'} : (@all (_102316 -> Prop)) = (@all (_102316 -> Prop)).
Proof. exact (eq_refl (@all (_102316 -> Prop))). Qed.
Lemma lem4070012 {_102316 _87604 : Type'} (s : _102316 -> Prop) (f : _102316 -> _87604) : (term273 _102316 _87604 s f) = (term273 _102316 _87604 s f).
Proof. exact (MK_COMB (@lem4070011 _102316) (@lem4070010 _102316 _87604 s f)). Qed.
Lemma lem4070013 {_102316 _87604 : Type'} (f : _102316 -> _87604) : (term274 _102316 _87604 f) = (term274 _102316 _87604 f).
Proof. exact (fun_ext (fun s : _102316 -> Prop => @lem4070012 _102316 _87604 s f)). Qed.
Lemma lem4070014 {_102316 : Type'} : (@all (_102316 -> Prop)) = (@all (_102316 -> Prop)).
Proof. exact (eq_refl (@all (_102316 -> Prop))). Qed.
Lemma lem4070015 {_102316 _87604 : Type'} (f : _102316 -> _87604) : (term275 _102316 _87604 f) = (term275 _102316 _87604 f).
Proof. exact (MK_COMB (@lem4070014 _102316) (@lem4070013 _102316 _87604 f)). Qed.
Lemma lem4070016 {_102316 _87604 : Type'} : (term276 _102316 _87604) = (term276 _102316 _87604).
Proof. exact (fun_ext (fun f : _102316 -> _87604 => @lem4070015 _102316 _87604 f)). Qed.
Lemma lem4070017 {_102316 _87604 : Type'} : (@all (_102316 -> _87604)) = (@all (_102316 -> _87604)).
Proof. exact (eq_refl (@all (_102316 -> _87604))). Qed.
Lemma lem4070018 {_102316 _87604 : Type'} : (term156 _102316 _87604) = (term156 _102316 _87604).
Proof. exact (MK_COMB (@lem4070017 _102316 _87604) (@lem4070016 _102316 _87604)). Qed.
Lemma lem4070019 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4070020 {_102316 _87604 : Type'} : (term198 _102316 _87604) = (term198 _102316 _87604).
Proof. exact (MK_COMB (@lem4070019) (@lem4070018 _102316 _87604)). Qed.
Lemma lem4070021 {_102289 _102316 _87593 _87604 A B : Type'} : (term213 _102289 _102316 _87593 _87604 A B) = (term213 _102289 _102316 _87593 _87604 A B).
Proof. exact (MK_COMB (@lem4070020 _102316 _87604) (@lem4070004 _102289 _102316 _87593 A B)). Qed.
Lemma lem4070026 {_102289 B : Type'} (s : _102289 -> Prop) (f : _102289 -> B) (t : _102289 -> Prop) : (term271 _102289 B s f t) = (term271 _102289 B s f t).
Proof. exact (eq_refl (term271 _102289 B s f t)). Qed.
Lemma lem4070027 {_102289 B : Type'} (s : _102289 -> Prop) (f : _102289 -> B) : (term272 _102289 B s f) = (term272 _102289 B s f).
Proof. exact (fun_ext (fun t : _102289 -> Prop => @lem4070026 _102289 B s f t)). Qed.
Lemma lem4070028 {_102289 : Type'} : (@all (_102289 -> Prop)) = (@all (_102289 -> Prop)).
Proof. exact (eq_refl (@all (_102289 -> Prop))). Qed.
Lemma lem4070029 {_102289 B : Type'} (s : _102289 -> Prop) (f : _102289 -> B) : (term273 _102289 B s f) = (term273 _102289 B s f).
Proof. exact (MK_COMB (@lem4070028 _102289) (@lem4070027 _102289 B s f)). Qed.
Lemma lem4070030 {_102289 B : Type'} (f : _102289 -> B) : (term274 _102289 B f) = (term274 _102289 B f).
Proof. exact (fun_ext (fun s : _102289 -> Prop => @lem4070029 _102289 B s f)). Qed.
Lemma lem4070031 {_102289 : Type'} : (@all (_102289 -> Prop)) = (@all (_102289 -> Prop)).
Proof. exact (eq_refl (@all (_102289 -> Prop))). Qed.
Lemma lem4070032 {_102289 B : Type'} (f : _102289 -> B) : (term275 _102289 B f) = (term275 _102289 B f).
Proof. exact (MK_COMB (@lem4070031 _102289) (@lem4070030 _102289 B f)). Qed.
Lemma lem4070033 {_102289 B : Type'} : (term276 _102289 B) = (term276 _102289 B).
Proof. exact (fun_ext (fun f : _102289 -> B => @lem4070032 _102289 B f)). Qed.
Lemma lem4070034 {_102289 B : Type'} : (@all (_102289 -> B)) = (@all (_102289 -> B)).
Proof. exact (eq_refl (@all (_102289 -> B))). Qed.
Lemma lem4070035 {_102289 B : Type'} : (term156 _102289 B) = (term156 _102289 B).
Proof. exact (MK_COMB (@lem4070034 _102289 B) (@lem4070033 _102289 B)). Qed.
Lemma lem4070036 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4070037 {_102289 B : Type'} : (term198 _102289 B) = (term198 _102289 B).
Proof. exact (MK_COMB (@lem4070036) (@lem4070035 _102289 B)). Qed.
Lemma lem4070038 {_102289 _102316 _87593 _87604 A B : Type'} : (term215 _102289 _102316 _87593 _87604 A B) = (term215 _102289 _102316 _87593 _87604 A B).
Proof. exact (MK_COMB (@lem4070037 _102289 B) (@lem4070021 _102289 _102316 _87593 _87604 A B)). Qed.
Lemma lem4070043 {_102289 _87604 : Type'} (s : _102289 -> Prop) (f : _102289 -> _87604) (t : _102289 -> Prop) : (term271 _102289 _87604 s f t) = (term271 _102289 _87604 s f t).
Proof. exact (eq_refl (term271 _102289 _87604 s f t)). Qed.
Lemma lem4070044 {_102289 _87604 : Type'} (s : _102289 -> Prop) (f : _102289 -> _87604) : (term272 _102289 _87604 s f) = (term272 _102289 _87604 s f).
Proof. exact (fun_ext (fun t : _102289 -> Prop => @lem4070043 _102289 _87604 s f t)). Qed.
Lemma lem4070045 {_102289 : Type'} : (@all (_102289 -> Prop)) = (@all (_102289 -> Prop)).
Proof. exact (eq_refl (@all (_102289 -> Prop))). Qed.
Lemma lem4070046 {_102289 _87604 : Type'} (s : _102289 -> Prop) (f : _102289 -> _87604) : (term273 _102289 _87604 s f) = (term273 _102289 _87604 s f).
Proof. exact (MK_COMB (@lem4070045 _102289) (@lem4070044 _102289 _87604 s f)). Qed.
Lemma lem4070047 {_102289 _87604 : Type'} (f : _102289 -> _87604) : (term274 _102289 _87604 f) = (term274 _102289 _87604 f).
Proof. exact (fun_ext (fun s : _102289 -> Prop => @lem4070046 _102289 _87604 s f)). Qed.
Lemma lem4070048 {_102289 : Type'} : (@all (_102289 -> Prop)) = (@all (_102289 -> Prop)).
Proof. exact (eq_refl (@all (_102289 -> Prop))). Qed.
Lemma lem4070049 {_102289 _87604 : Type'} (f : _102289 -> _87604) : (term275 _102289 _87604 f) = (term275 _102289 _87604 f).
Proof. exact (MK_COMB (@lem4070048 _102289) (@lem4070047 _102289 _87604 f)). Qed.
Lemma lem4070050 {_102289 _87604 : Type'} : (term276 _102289 _87604) = (term276 _102289 _87604).
Proof. exact (fun_ext (fun f : _102289 -> _87604 => @lem4070049 _102289 _87604 f)). Qed.
Lemma lem4070051 {_102289 _87604 : Type'} : (@all (_102289 -> _87604)) = (@all (_102289 -> _87604)).
Proof. exact (eq_refl (@all (_102289 -> _87604))). Qed.
Lemma lem4070052 {_102289 _87604 : Type'} : (term156 _102289 _87604) = (term156 _102289 _87604).
Proof. exact (MK_COMB (@lem4070051 _102289 _87604) (@lem4070050 _102289 _87604)). Qed.
Lemma lem4070053 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4070054 {_102289 _87604 : Type'} : (term198 _102289 _87604) = (term198 _102289 _87604).
Proof. exact (MK_COMB (@lem4070053) (@lem4070052 _102289 _87604)). Qed.
Lemma lem4070055 {_102289 _102316 _87593 _87604 A B : Type'} : (term217 _102289 _102316 _87593 _87604 A B) = (term217 _102289 _102316 _87593 _87604 A B).
Proof. exact (MK_COMB (@lem4070054 _102289 _87604) (@lem4070038 _102289 _102316 _87593 _87604 A B)). Qed.
Lemma lem4070060 {_102289 _102316 : Type'} (s : _102289 -> Prop) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term271 _102289 _102316 s f t) = (term271 _102289 _102316 s f t).
Proof. exact (eq_refl (term271 _102289 _102316 s f t)). Qed.
Lemma lem4070061 {_102289 _102316 : Type'} (s : _102289 -> Prop) (f : _102289 -> _102316) : (term272 _102289 _102316 s f) = (term272 _102289 _102316 s f).
Proof. exact (fun_ext (fun t : _102289 -> Prop => @lem4070060 _102289 _102316 s f t)). Qed.
Lemma lem4070062 {_102289 : Type'} : (@all (_102289 -> Prop)) = (@all (_102289 -> Prop)).
Proof. exact (eq_refl (@all (_102289 -> Prop))). Qed.
Lemma lem4070063 {_102289 _102316 : Type'} (s : _102289 -> Prop) (f : _102289 -> _102316) : (term273 _102289 _102316 s f) = (term273 _102289 _102316 s f).
Proof. exact (MK_COMB (@lem4070062 _102289) (@lem4070061 _102289 _102316 s f)). Qed.
Lemma lem4070064 {_102289 _102316 : Type'} (f : _102289 -> _102316) : (term274 _102289 _102316 f) = (term274 _102289 _102316 f).
Proof. exact (fun_ext (fun s : _102289 -> Prop => @lem4070063 _102289 _102316 s f)). Qed.
Lemma lem4070065 {_102289 : Type'} : (@all (_102289 -> Prop)) = (@all (_102289 -> Prop)).
Proof. exact (eq_refl (@all (_102289 -> Prop))). Qed.
Lemma lem4070066 {_102289 _102316 : Type'} (f : _102289 -> _102316) : (term275 _102289 _102316 f) = (term275 _102289 _102316 f).
Proof. exact (MK_COMB (@lem4070065 _102289) (@lem4070064 _102289 _102316 f)). Qed.
Lemma lem4070067 {_102289 _102316 : Type'} : (term276 _102289 _102316) = (term276 _102289 _102316).
Proof. exact (fun_ext (fun f : _102289 -> _102316 => @lem4070066 _102289 _102316 f)). Qed.
Lemma lem4070068 {_102289 _102316 : Type'} : (@all (_102289 -> _102316)) = (@all (_102289 -> _102316)).
Proof. exact (eq_refl (@all (_102289 -> _102316))). Qed.
Lemma lem4070069 {_102289 _102316 : Type'} : (term156 _102289 _102316) = (term156 _102289 _102316).
Proof. exact (MK_COMB (@lem4070068 _102289 _102316) (@lem4070067 _102289 _102316)). Qed.
Lemma lem4070070 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4070071 {_102289 _102316 : Type'} : (term198 _102289 _102316) = (term198 _102289 _102316).
Proof. exact (MK_COMB (@lem4070070) (@lem4070069 _102289 _102316)). Qed.
Lemma lem4070072 {_102289 _102316 _87593 _87604 A B : Type'} : (term219 _102289 _102316 _87593 _87604 A B) = (term219 _102289 _102316 _87593 _87604 A B).
Proof. exact (MK_COMB (@lem4070071 _102289 _102316) (@lem4070055 _102289 _102316 _87593 _87604 A B)). Qed.
Lemma lem4070085 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (t : _102316 -> Prop) : (term283 _102289 _102316 n f s P t) = (term283 _102289 _102316 n f s P t).
Proof. exact (eq_refl (term283 _102289 _102316 n f s P t)). Qed.
Lemma lem4070086 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term284 _102289 _102316 n f s P) = (term284 _102289 _102316 n f s P).
Proof. exact (fun_ext (fun t : _102316 -> Prop => @lem4070085 _102289 _102316 n f s P t)). Qed.
Lemma lem4070087 {_102316 : Type'} : (@ex (_102316 -> Prop)) = (@ex (_102316 -> Prop)).
Proof. exact (eq_refl (@ex (_102316 -> Prop))). Qed.
Lemma lem4070088 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term14 _102289 _102316 n f s P) = (term14 _102289 _102316 n f s P).
Proof. exact (MK_COMB (@lem4070087 _102316) (@lem4070086 _102289 _102316 n f s P)). Qed.
Lemma lem4070101 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term45 _102289 _102316 n s P f t) = (term45 _102289 _102316 n s P f t).
Proof. exact (eq_refl (term45 _102289 _102316 n s P f t)). Qed.
Lemma lem4070102 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term46 _102289 _102316 n s P f) = (term46 _102289 _102316 n s P f).
Proof. exact (fun_ext (fun t : _102289 -> Prop => @lem4070101 _102289 _102316 n s P f t)). Qed.
Lemma lem4070103 {_102289 : Type'} : (@ex (_102289 -> Prop)) = (@ex (_102289 -> Prop)).
Proof. exact (eq_refl (@ex (_102289 -> Prop))). Qed.
Lemma lem4070104 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term18 _102289 _102316 n s P f) = (term18 _102289 _102316 n s P f).
Proof. exact (MK_COMB (@lem4070103 _102289) (@lem4070102 _102289 _102316 n s P f)). Qed.
Lemma lem4070105 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4070106 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term285 _102289 _102316 n s P f) = (term285 _102289 _102316 n s P f).
Proof. exact (MK_COMB (@lem4070105) (@lem4070104 _102289 _102316 n s P f)). Qed.
Lemma lem4070107 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term148 _102289 _102316 n f s P) = (term148 _102289 _102316 n f s P).
Proof. exact (MK_COMB (@lem4070106 _102289 _102316 n s P f) (@lem4070088 _102289 _102316 n f s P)). Qed.
Lemma lem4070108 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4070109 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term150 _102289 _102316 n f s P) = (term150 _102289 _102316 n f s P).
Proof. exact (MK_COMB (@lem4070108) (@lem4070107 _102289 _102316 n f s P)). Qed.
Lemma lem4070110 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4070111 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term220 _102289 _102316 n f s P) = (term220 _102289 _102316 n f s P).
Proof. exact (MK_COMB (@lem4070110) (@lem4070109 _102289 _102316 n f s P)). Qed.
Lemma lem4070112 {_102289 _102316 _87593 _87604 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term221 _102289 _102316 _87593 _87604 A B n f s P) = (term221 _102289 _102316 _87593 _87604 A B n f s P).
Proof. exact (MK_COMB (@lem4070111 _102289 _102316 n f s P) (@lem4070072 _102289 _102316 _87593 _87604 A B)). Qed.
Lemma lem4070113 {_102289 _102316 _87593 _87604 A B : Type'} (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term223 _102289 _102316 _87593 _87604 A B f s P) = (term223 _102289 _102316 _87593 _87604 A B f s P).
Proof. exact (fun_ext (fun n : nat => @lem4070112 _102289 _102316 _87593 _87604 A B n f s P)). Qed.
Lemma lem4070114 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4070115 {_102289 _102316 _87593 _87604 A B : Type'} (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term225 _102289 _102316 _87593 _87604 A B f s P) = (term225 _102289 _102316 _87593 _87604 A B f s P).
Proof. exact (MK_COMB (@lem4070114) (@lem4070113 _102289 _102316 _87593 _87604 A B f s P)). Qed.
Lemma lem4070116 {_102289 _102316 _87593 _87604 A B : Type'} (s : _102289 -> Prop) (P : type686 _102316) : (term227 _102289 _102316 _87593 _87604 A B s P) = (term227 _102289 _102316 _87593 _87604 A B s P).
Proof. exact (fun_ext (fun f : _102289 -> _102316 => @lem4070115 _102289 _102316 _87593 _87604 A B f s P)). Qed.
Lemma lem4070117 {_102289 _102316 : Type'} : (@all (_102289 -> _102316)) = (@all (_102289 -> _102316)).
Proof. exact (eq_refl (@all (_102289 -> _102316))). Qed.
Lemma lem4070118 {_102289 _102316 _87593 _87604 A B : Type'} (s : _102289 -> Prop) (P : type686 _102316) : (term229 _102289 _102316 _87593 _87604 A B s P) = (term229 _102289 _102316 _87593 _87604 A B s P).
Proof. exact (MK_COMB (@lem4070117 _102289 _102316) (@lem4070116 _102289 _102316 _87593 _87604 A B s P)). Qed.
Lemma lem4070119 {_102289 _102316 _87593 _87604 A B : Type'} (P : type686 _102316) : (term231 _102289 _102316 _87593 _87604 A B P) = (term231 _102289 _102316 _87593 _87604 A B P).
Proof. exact (fun_ext (fun s : _102289 -> Prop => @lem4070118 _102289 _102316 _87593 _87604 A B s P)). Qed.
Lemma lem4070120 {_102289 : Type'} : (@all (_102289 -> Prop)) = (@all (_102289 -> Prop)).
Proof. exact (eq_refl (@all (_102289 -> Prop))). Qed.
Lemma lem4070121 {_102289 _102316 _87593 _87604 A B : Type'} (P : type686 _102316) : (term233 _102289 _102316 _87593 _87604 A B P) = (term233 _102289 _102316 _87593 _87604 A B P).
Proof. exact (MK_COMB (@lem4070120 _102289) (@lem4070119 _102289 _102316 _87593 _87604 A B P)). Qed.
Lemma lem4070122 {_102289 _102316 _87593 _87604 A B : Type'} : (term235 _102289 _102316 _87593 _87604 A B) = (term235 _102289 _102316 _87593 _87604 A B).
Proof. exact (fun_ext (fun P : type686 _102316 => @lem4070121 _102289 _102316 _87593 _87604 A B P)). Qed.
Lemma lem4070123 {_102316 : Type'} : (@all ((_102316 -> Prop) -> Prop)) = (@all ((_102316 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_102316 -> Prop) -> Prop))). Qed.
Lemma lem4070124 {_102289 _102316 _87593 _87604 A B : Type'} : (term237 _102289 _102316 _87593 _87604 A B) = (term237 _102289 _102316 _87593 _87604 A B).
Proof. exact (MK_COMB (@lem4070123 _102316) (@lem4070122 _102289 _102316 _87593 _87604 A B)). Qed.
Lemma lem4070635 {_102289 _102316 _87593 _87604 A B : Type'} : (term236 _102289 _102316 _87593 _87604 A B) = (term237 _102289 _102316 _87593 _87604 A B).
Proof. exact (TRANS (@lem4069697 _102289 _102316 _87593 _87604 A B) (@lem4070124 _102289 _102316 _87593 _87604 A B)). Qed.
Lemma lem4070636 {_102289 _102316 _87593 _87604 A B : Type'} : (term237 _102289 _102316 _87593 _87604 A B) = (term236 _102289 _102316 _87593 _87604 A B).
Proof. exact (SYM (@lem4070635 _102289 _102316 _87593 _87604 A B)). Qed.
Lemma lem4070637 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term150 _102289 _102316 n f s P) : term150 _102289 _102316 n f s P.
Proof. exact (h1). Qed.
Lemma lem4070638 {_102289 _102316 : Type'} (h1 : term156 _102289 _102316) : term156 _102289 _102316.
Proof. exact (h1). Qed.
Lemma lem4070649 (h1 : term264) : term264.
Proof. exact (h1). Qed.
Lemma lem4070650 {_102289 _102316 : Type'} (h1 : term153 _102289 _102316) : term153 _102289 _102316.
Proof. exact (h1). Qed.
Lemma lem4070657 {_102289 _102316 : Type'} (h1 : term151 _102289 _102316) : term151 _102289 _102316.
Proof. exact (h1). Qed.
Lemma lem4070674 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term45 _102289 _102316 n s P f t) = (term45 _102289 _102316 n s P f t).
Proof. exact (eq_refl (term45 _102289 _102316 n s P f t)). Qed.
Lemma lem4070675 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term46 _102289 _102316 n s P f) = (term46 _102289 _102316 n s P f).
Proof. exact (fun_ext (fun t : _102289 -> Prop => @lem4070674 _102289 _102316 n s P f t)). Qed.
Lemma lem4070676 {_102289 : Type'} : (@ex (_102289 -> Prop)) = (@ex (_102289 -> Prop)).
Proof. exact (eq_refl (@ex (_102289 -> Prop))). Qed.
Lemma lem4070677 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term18 _102289 _102316 n s P f) = (term18 _102289 _102316 n s P f).
Proof. exact (MK_COMB (@lem4070676 _102289) (@lem4070675 _102289 _102316 n s P f)). Qed.
Lemma lem4070686 {_102289 _102316 : Type'} (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (t : _102316 -> Prop) : (term286 _102289 _102316 f s P t) = (term287 _102289 _102316 f s P t).
Proof. exact (@lem17045 (term288 _102289 _102316 t f s) (P t)). Qed.
Lemma lem4070688 {_102316 : Type'} (t : _102316 -> Prop) (n : nat) : (term85 _102316 t n) = (term85 _102316 t n).
Proof. exact (eq_refl (term85 _102316 t n)). Qed.
Lemma lem4070689 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (t : _102316 -> Prop) : (term289 _102289 _102316 n f s P t) = (term290 _102289 _102316 n f s P t).
Proof. exact (MK_COMB (@lem4070688 _102316 t n) (@lem4070686 _102289 _102316 f s P t)). Qed.
Lemma lem4070690 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (t : _102316 -> Prop) : (term291 _102289 _102316 n f s P t) = (term289 _102289 _102316 n f s P t).
Proof. exact (@lem17045 (term89 _102316 t n) (term292 _102289 _102316 f s P t)). Qed.
Lemma lem4070691 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (t : _102316 -> Prop) : (term291 _102289 _102316 n f s P t) = (term290 _102289 _102316 n f s P t).
Proof. exact (TRANS (@lem4070690 _102289 _102316 n f s P t) (@lem4070689 _102289 _102316 n f s P t)). Qed.
Lemma lem4070693 {_102316 : Type'} (t : _102316 -> Prop) : (term91 _102316 t) = (term91 _102316 t).
Proof. exact (eq_refl (term91 _102316 t)). Qed.
Lemma lem4070694 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (t : _102316 -> Prop) : (term293 _102289 _102316 n f s P t) = (term294 _102289 _102316 n f s P t).
Proof. exact (MK_COMB (@lem4070693 _102316 t) (@lem4070691 _102289 _102316 n f s P t)). Qed.
Lemma lem4070695 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (t : _102316 -> Prop) : (term295 _102289 _102316 n f s P t) = (term293 _102289 _102316 n f s P t).
Proof. exact (@lem17045 (@FINITE _102316 t) (term296 _102289 _102316 n f s P t)). Qed.
Lemma lem4070696 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (t : _102316 -> Prop) : (term295 _102289 _102316 n f s P t) = (term294 _102289 _102316 n f s P t).
Proof. exact (TRANS (@lem4070695 _102289 _102316 n f s P t) (@lem4070694 _102289 _102316 n f s P t)). Qed.
Lemma lem4070697 {_102316 : Type'} (P : type686 _102316) : (term96 _102316 P) = (term97 _102316 P).
Proof. exact (@lem18394 (_102316 -> Prop) P). Qed.
Lemma lem4070698 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term297 _102289 _102316 n f s P) = (term298 _102289 _102316 n f s P).
Proof. exact (@lem4070697 _102316 (term284 _102289 _102316 n f s P)). Qed.
Lemma lem4070699 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (t : _102316 -> Prop) : (term299 _102289 _102316 n f s P t) = (term283 _102289 _102316 n f s P t).
Proof. exact (eq_refl (term299 _102289 _102316 n f s P t)). Qed.
Lemma lem4070700 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4070701 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (t : _102316 -> Prop) : (term300 _102289 _102316 n f s P t) = (term295 _102289 _102316 n f s P t).
Proof. exact (MK_COMB (@lem4070700) (@lem4070699 _102289 _102316 n f s P t)). Qed.
Lemma lem4070702 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (t : _102316 -> Prop) : (term300 _102289 _102316 n f s P t) = (term294 _102289 _102316 n f s P t).
Proof. exact (TRANS (@lem4070701 _102289 _102316 n f s P t) (@lem4070696 _102289 _102316 n f s P t)). Qed.
Lemma lem4070703 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term301 _102289 _102316 n f s P) = (term302 _102289 _102316 n f s P).
Proof. exact (fun_ext (fun t : _102316 -> Prop => @lem4070702 _102289 _102316 n f s P t)). Qed.
Lemma lem4070704 {_102316 : Type'} : (@all (_102316 -> Prop)) = (@all (_102316 -> Prop)).
Proof. exact (eq_refl (@all (_102316 -> Prop))). Qed.
Lemma lem4070705 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term298 _102289 _102316 n f s P) = (term303 _102289 _102316 n f s P).
Proof. exact (MK_COMB (@lem4070704 _102316) (@lem4070703 _102289 _102316 n f s P)). Qed.
Lemma lem4070706 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term297 _102289 _102316 n f s P) = (term303 _102289 _102316 n f s P).
Proof. exact (TRANS (@lem4070698 _102289 _102316 n f s P) (@lem4070705 _102289 _102316 n f s P)). Qed.
Lemma lem4070707 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4070708 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term304 _102289 _102316 n s P f) = (term304 _102289 _102316 n s P f).
Proof. exact (MK_COMB (@lem4070707) (@lem4070677 _102289 _102316 n s P f)). Qed.
Lemma lem4070709 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term305 _102289 _102316 n f s P) = (term306 _102289 _102316 n f s P).
Proof. exact (MK_COMB (@lem4070708 _102289 _102316 n s P f) (@lem4070706 _102289 _102316 n f s P)). Qed.
Lemma lem4070710 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term150 _102289 _102316 n f s P) = (term305 _102289 _102316 n f s P).
Proof. exact (@lem17362 (term18 _102289 _102316 n s P f) (term14 _102289 _102316 n f s P)). Qed.
Lemma lem4070711 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term150 _102289 _102316 n f s P) = (term306 _102289 _102316 n f s P).
Proof. exact (TRANS (@lem4070710 _102289 _102316 n f s P) (@lem4070709 _102289 _102316 n f s P)). Qed.
Lemma lem4070790 {A : Type'} (P : A -> Prop) (Q : Prop) : (term307 A P Q) = (term308 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4070791 {_102289 : Type'} (P : type686 _102289) (Q : Prop) : (term309 _102289 P Q) = (term310 _102289 P Q).
Proof. exact (@lem4070790 (_102289 -> Prop) P Q). Qed.
Lemma lem4070792 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term311 _102289 _102316 n f s P) = (term312 _102289 _102316 n f s P).
Proof. exact (@lem4070791 _102289 (term46 _102289 _102316 n s P f) (term303 _102289 _102316 n f s P)). Qed.
Lemma lem4070793 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term99 _102289 _102316 n s P f t) = (term45 _102289 _102316 n s P f t).
Proof. exact (eq_refl (term99 _102289 _102316 n s P f t)). Qed.
Lemma lem4070794 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term313 _102289 _102316 n s P f) = (term46 _102289 _102316 n s P f).
Proof. exact (fun_ext (fun t : _102289 -> Prop => @lem4070793 _102289 _102316 n s P f t)). Qed.
Lemma lem4070795 {_102289 : Type'} : (@ex (_102289 -> Prop)) = (@ex (_102289 -> Prop)).
Proof. exact (eq_refl (@ex (_102289 -> Prop))). Qed.
Lemma lem4070796 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term314 _102289 _102316 n s P f) = (term18 _102289 _102316 n s P f).
Proof. exact (MK_COMB (@lem4070795 _102289) (@lem4070794 _102289 _102316 n s P f)). Qed.
Lemma lem4070797 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4070798 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term315 _102289 _102316 n s P f) = (term304 _102289 _102316 n s P f).
Proof. exact (MK_COMB (@lem4070797) (@lem4070796 _102289 _102316 n s P f)). Qed.
Lemma lem4070799 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term303 _102289 _102316 n f s P) = (term303 _102289 _102316 n f s P).
Proof. exact (eq_refl (term303 _102289 _102316 n f s P)). Qed.
Lemma lem4070800 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term311 _102289 _102316 n f s P) = (term306 _102289 _102316 n f s P).
Proof. exact (MK_COMB (@lem4070798 _102289 _102316 n s P f) (@lem4070799 _102289 _102316 n f s P)). Qed.
Lemma lem4070801 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4070802 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term316 _102289 _102316 n f s P) = (term317 _102289 _102316 n f s P).
Proof. exact (MK_COMB (@lem4070801) (@lem4070800 _102289 _102316 n f s P)). Qed.
Lemma lem4070803 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term99 _102289 _102316 n s P f t) = (term45 _102289 _102316 n s P f t).
Proof. exact (eq_refl (term99 _102289 _102316 n s P f t)). Qed.
Lemma lem4070804 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4070805 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term318 _102289 _102316 n s P f t) = (term319 _102289 _102316 n s P f t).
Proof. exact (MK_COMB (@lem4070804) (@lem4070803 _102289 _102316 n s P f t)). Qed.
Lemma lem4070806 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term303 _102289 _102316 n f s P) = (term303 _102289 _102316 n f s P).
Proof. exact (eq_refl (term303 _102289 _102316 n f s P)). Qed.
Lemma lem4070807 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term320 _102289 _102316 t n f s P) = (term321 _102289 _102316 t n f s P).
Proof. exact (MK_COMB (@lem4070805 _102289 _102316 n s P f t) (@lem4070806 _102289 _102316 n f s P)). Qed.
Lemma lem4070808 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term322 _102289 _102316 n f s P) = (term323 _102289 _102316 n f s P).
Proof. exact (fun_ext (fun t : _102289 -> Prop => @lem4070807 _102289 _102316 t n f s P)). Qed.
Lemma lem4070809 {_102289 : Type'} : (@ex (_102289 -> Prop)) = (@ex (_102289 -> Prop)).
Proof. exact (eq_refl (@ex (_102289 -> Prop))). Qed.
Lemma lem4070810 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term312 _102289 _102316 n f s P) = (term324 _102289 _102316 n f s P).
Proof. exact (MK_COMB (@lem4070809 _102289) (@lem4070808 _102289 _102316 n f s P)). Qed.
Lemma lem4070811 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : ((term311 _102289 _102316 n f s P) = (term312 _102289 _102316 n f s P)) = ((term306 _102289 _102316 n f s P) = (term324 _102289 _102316 n f s P)).
Proof. exact (MK_COMB (@lem4070802 _102289 _102316 n f s P) (@lem4070810 _102289 _102316 n f s P)). Qed.
Lemma lem4070813 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term306 _102289 _102316 n f s P) = (term324 _102289 _102316 n f s P).
Proof. exact (EQ_MP (@lem4070811 _102289 _102316 n f s P) (@lem4070792 _102289 _102316 n f s P)). Qed.
Lemma lem4070814 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term150 _102289 _102316 n f s P) = (term324 _102289 _102316 n f s P).
Proof. exact (TRANS (@lem4070711 _102289 _102316 n f s P) (@lem4070813 _102289 _102316 n f s P)). Qed.
Lemma lem4070815 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term150 _102289 _102316 n f s P) : term324 _102289 _102316 n f s P.
Proof. exact (EQ_MP (@lem4070814 _102289 _102316 n f s P) (@lem4070637 _102289 _102316 n f s P h1)). Qed.
Lemma lem4070822 {_102289 _102316 : Type'} (s : _102289 -> Prop) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term271 _102289 _102316 s f t) = (term325 _102289 _102316 s f t).
Proof. exact (@lem17265 (@SUBSET _102289 s t) (term326 _102289 _102316 s f t)). Qed.
Lemma lem4070823 {_102289 _102316 : Type'} (s : _102289 -> Prop) (f : _102289 -> _102316) : (term272 _102289 _102316 s f) = (term327 _102289 _102316 s f).
Proof. exact (fun_ext (fun t : _102289 -> Prop => @lem4070822 _102289 _102316 s f t)). Qed.
Lemma lem4070824 {_102289 : Type'} : (@all (_102289 -> Prop)) = (@all (_102289 -> Prop)).
Proof. exact (eq_refl (@all (_102289 -> Prop))). Qed.
Lemma lem4070825 {_102289 _102316 : Type'} (s : _102289 -> Prop) (f : _102289 -> _102316) : (term273 _102289 _102316 s f) = (term328 _102289 _102316 s f).
Proof. exact (MK_COMB (@lem4070824 _102289) (@lem4070823 _102289 _102316 s f)). Qed.
Lemma lem4070826 {_102289 _102316 : Type'} (f : _102289 -> _102316) : (term274 _102289 _102316 f) = (term329 _102289 _102316 f).
Proof. exact (fun_ext (fun s : _102289 -> Prop => @lem4070825 _102289 _102316 s f)). Qed.
Lemma lem4070827 {_102289 : Type'} : (@all (_102289 -> Prop)) = (@all (_102289 -> Prop)).
Proof. exact (eq_refl (@all (_102289 -> Prop))). Qed.
Lemma lem4070828 {_102289 _102316 : Type'} (f : _102289 -> _102316) : (term275 _102289 _102316 f) = (term330 _102289 _102316 f).
Proof. exact (MK_COMB (@lem4070827 _102289) (@lem4070826 _102289 _102316 f)). Qed.
Lemma lem4070829 {_102289 _102316 : Type'} : (term276 _102289 _102316) = (term331 _102289 _102316).
Proof. exact (fun_ext (fun f : _102289 -> _102316 => @lem4070828 _102289 _102316 f)). Qed.
Lemma lem4070830 {_102289 _102316 : Type'} : (@all (_102289 -> _102316)) = (@all (_102289 -> _102316)).
Proof. exact (eq_refl (@all (_102289 -> _102316))). Qed.
Lemma lem4070891 {_102289 _102316 : Type'} : (term156 _102289 _102316) = (term332 _102289 _102316).
Proof. exact (MK_COMB (@lem4070830 _102289 _102316) (@lem4070829 _102289 _102316)). Qed.
Lemma lem4070892 {_102289 _102316 : Type'} (h1 : term156 _102289 _102316) : term332 _102289 _102316.
Proof. exact (EQ_MP (@lem4070891 _102289 _102316) (@lem4070638 _102289 _102316 h1)). Qed.
Lemma lem4071669 (m : nat) (n : nat) (p : nat) : (term333 m n p) = (term334 m n p).
Proof. exact (@lem17045 (Peano.le m n) (Peano.lt n p)). Qed.
Lemma lem4071670 (m : nat) (p : nat) : (Peano.lt m p) = (Peano.lt m p).
Proof. exact (eq_refl (Peano.lt m p)). Qed.
Lemma lem4071671 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4071672 (m : nat) (n : nat) (p : nat) : (term335 m n p) = (term336 m n p).
Proof. exact (MK_COMB (@lem4071671) (@lem4071669 m n p)). Qed.
Lemma lem4071673 (n : nat) (m : nat) (p : nat) : (term337 n m p) = (term338 n m p).
Proof. exact (MK_COMB (@lem4071672 m n p) (@lem4071670 m p)). Qed.
Lemma lem4071674 (n : nat) (m : nat) (p : nat) : (term258 n m p) = (term337 n m p).
Proof. exact (@lem17265 (term339 m n p) (Peano.lt m p)). Qed.
Lemma lem4071675 (n : nat) (m : nat) (p : nat) : (term258 n m p) = (term338 n m p).
Proof. exact (TRANS (@lem4071674 n m p) (@lem4071673 n m p)). Qed.
Lemma lem4071676 (n : nat) (m : nat) : (term259 n m) = (term340 n m).
Proof. exact (fun_ext (fun p : nat => @lem4071675 n m p)). Qed.
Lemma lem4071677 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4071678 (n : nat) (m : nat) : (term260 n m) = (term341 n m).
Proof. exact (MK_COMB (@lem4071677) (@lem4071676 n m)). Qed.
Lemma lem4071679 (m : nat) : (term261 m) = (term342 m).
Proof. exact (fun_ext (fun n : nat => @lem4071678 n m)). Qed.
Lemma lem4071680 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4071681 (m : nat) : (term262 m) = (term343 m).
Proof. exact (MK_COMB (@lem4071680) (@lem4071679 m)). Qed.
Lemma lem4071682 : term263 = term344.
Proof. exact (fun_ext (fun m : nat => @lem4071681 m)). Qed.
Lemma lem4071683 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4071744 : term264 = term345.
Proof. exact (MK_COMB (@lem4071683) (@lem4071682)). Qed.
Lemma lem4071745 (h1 : term264) : term345.
Proof. exact (EQ_MP (@lem4071744) (@lem4070649 h1)). Qed.
Lemma lem4071752 {_102289 _102316 : Type'} (f : _102289 -> _102316) (s : _102289 -> Prop) : (term250 _102289 _102316 f s) = (term346 _102289 _102316 f s).
Proof. exact (@lem17265 (@FINITE _102289 s) (term347 _102289 _102316 f s)). Qed.
Lemma lem4071753 {_102289 _102316 : Type'} (f : _102289 -> _102316) : (term251 _102289 _102316 f) = (term348 _102289 _102316 f).
Proof. exact (fun_ext (fun s : _102289 -> Prop => @lem4071752 _102289 _102316 f s)). Qed.
Lemma lem4071754 {_102289 : Type'} : (@all (_102289 -> Prop)) = (@all (_102289 -> Prop)).
Proof. exact (eq_refl (@all (_102289 -> Prop))). Qed.
Lemma lem4071755 {_102289 _102316 : Type'} (f : _102289 -> _102316) : (term252 _102289 _102316 f) = (term349 _102289 _102316 f).
Proof. exact (MK_COMB (@lem4071754 _102289) (@lem4071753 _102289 _102316 f)). Qed.
Lemma lem4071756 {_102289 _102316 : Type'} : (term253 _102289 _102316) = (term350 _102289 _102316).
Proof. exact (fun_ext (fun f : _102289 -> _102316 => @lem4071755 _102289 _102316 f)). Qed.
Lemma lem4071757 {_102289 _102316 : Type'} : (@all (_102289 -> _102316)) = (@all (_102289 -> _102316)).
Proof. exact (eq_refl (@all (_102289 -> _102316))). Qed.
Lemma lem4071814 {_102289 _102316 : Type'} : (term153 _102289 _102316) = (term351 _102289 _102316).
Proof. exact (MK_COMB (@lem4071757 _102289 _102316) (@lem4071756 _102289 _102316)). Qed.
Lemma lem4071815 {_102289 _102316 : Type'} (h1 : term153 _102289 _102316) : term351 _102289 _102316.
Proof. exact (EQ_MP (@lem4071814 _102289 _102316) (@lem4070650 _102289 _102316 h1)). Qed.
Lemma lem4072242 {_102289 _102316 : Type'} (f : _102289 -> _102316) (s : _102289 -> Prop) : (term242 _102289 _102316 f s) = (term352 _102289 _102316 f s).
Proof. exact (@lem17265 (@FINITE _102289 s) (term353 _102289 _102316 f s)). Qed.
Lemma lem4072243 {_102289 _102316 : Type'} (f : _102289 -> _102316) : (term243 _102289 _102316 f) = (term354 _102289 _102316 f).
Proof. exact (fun_ext (fun s : _102289 -> Prop => @lem4072242 _102289 _102316 f s)). Qed.
Lemma lem4072244 {_102289 : Type'} : (@all (_102289 -> Prop)) = (@all (_102289 -> Prop)).
Proof. exact (eq_refl (@all (_102289 -> Prop))). Qed.
Lemma lem4072245 {_102289 _102316 : Type'} (f : _102289 -> _102316) : (term244 _102289 _102316 f) = (term355 _102289 _102316 f).
Proof. exact (MK_COMB (@lem4072244 _102289) (@lem4072243 _102289 _102316 f)). Qed.
Lemma lem4072246 {_102289 _102316 : Type'} : (term245 _102289 _102316) = (term356 _102289 _102316).
Proof. exact (fun_ext (fun f : _102289 -> _102316 => @lem4072245 _102289 _102316 f)). Qed.
Lemma lem4072247 {_102289 _102316 : Type'} : (@all (_102289 -> _102316)) = (@all (_102289 -> _102316)).
Proof. exact (eq_refl (@all (_102289 -> _102316))). Qed.
Lemma lem4072304 {_102289 _102316 : Type'} : (term151 _102289 _102316) = (term357 _102289 _102316).
Proof. exact (MK_COMB (@lem4072247 _102289 _102316) (@lem4072246 _102289 _102316)). Qed.
Lemma lem4072305 {_102289 _102316 : Type'} (h1 : term151 _102289 _102316) : term357 _102289 _102316.
Proof. exact (EQ_MP (@lem4072304 _102289 _102316) (@lem4070657 _102289 _102316 h1)). Qed.
Lemma lem4072586 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term321 _102289 _102316 t n f s P) : term321 _102289 _102316 t n f s P.
Proof. exact (h1). Qed.
Lemma lem4072609 {_102289 _102316 : Type'} (s : _102289 -> Prop) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term325 _102289 _102316 s f t) = (term325 _102289 _102316 s f t).
Proof. exact (eq_refl (term325 _102289 _102316 s f t)). Qed.
Lemma lem4072610 {_102289 _102316 : Type'} (s : _102289 -> Prop) (f : _102289 -> _102316) : (term327 _102289 _102316 s f) = (term327 _102289 _102316 s f).
Proof. exact (fun_ext (fun t : _102289 -> Prop => @lem4072609 _102289 _102316 s f t)). Qed.
Lemma lem4072611 {_102289 : Type'} : (@all (_102289 -> Prop)) = (@all (_102289 -> Prop)).
Proof. exact (eq_refl (@all (_102289 -> Prop))). Qed.
Lemma lem4072612 {_102289 _102316 : Type'} (s : _102289 -> Prop) (f : _102289 -> _102316) : (term328 _102289 _102316 s f) = (term328 _102289 _102316 s f).
Proof. exact (MK_COMB (@lem4072611 _102289) (@lem4072610 _102289 _102316 s f)). Qed.
Lemma lem4072613 {_102289 _102316 : Type'} (f : _102289 -> _102316) : (term329 _102289 _102316 f) = (term329 _102289 _102316 f).
Proof. exact (fun_ext (fun s : _102289 -> Prop => @lem4072612 _102289 _102316 s f)). Qed.
Lemma lem4072614 {_102289 : Type'} : (@all (_102289 -> Prop)) = (@all (_102289 -> Prop)).
Proof. exact (eq_refl (@all (_102289 -> Prop))). Qed.
Lemma lem4072615 {_102289 _102316 : Type'} (f : _102289 -> _102316) : (term330 _102289 _102316 f) = (term330 _102289 _102316 f).
Proof. exact (MK_COMB (@lem4072614 _102289) (@lem4072613 _102289 _102316 f)). Qed.
Lemma lem4072616 {_102289 _102316 : Type'} : (term331 _102289 _102316) = (term331 _102289 _102316).
Proof. exact (fun_ext (fun f : _102289 -> _102316 => @lem4072615 _102289 _102316 f)). Qed.
Lemma lem4072617 {_102289 _102316 : Type'} : (@all (_102289 -> _102316)) = (@all (_102289 -> _102316)).
Proof. exact (eq_refl (@all (_102289 -> _102316))). Qed.
Lemma lem4072618 {_102289 _102316 : Type'} : (term332 _102289 _102316) = (term332 _102289 _102316).
Proof. exact (MK_COMB (@lem4072617 _102289 _102316) (@lem4072616 _102289 _102316)). Qed.
Lemma lem4072619 {_102289 _102316 : Type'} (h1 : term156 _102289 _102316) : term332 _102289 _102316.
Proof. exact (EQ_MP (@lem4072618 _102289 _102316) (@lem4070892 _102289 _102316 h1)). Qed.
Lemma lem4072974 (n : nat) (m : nat) (p : nat) : (term338 n m p) = (term338 n m p).
Proof. exact (eq_refl (term338 n m p)). Qed.
Lemma lem4072975 (n : nat) (m : nat) : (term340 n m) = (term340 n m).
Proof. exact (fun_ext (fun p : nat => @lem4072974 n m p)). Qed.
Lemma lem4072976 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4072977 (n : nat) (m : nat) : (term341 n m) = (term341 n m).
Proof. exact (MK_COMB (@lem4072976) (@lem4072975 n m)). Qed.
Lemma lem4072978 (m : nat) : (term342 m) = (term342 m).
Proof. exact (fun_ext (fun n : nat => @lem4072977 n m)). Qed.
Lemma lem4072979 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4072980 (m : nat) : (term343 m) = (term343 m).
Proof. exact (MK_COMB (@lem4072979) (@lem4072978 m)). Qed.
Lemma lem4072981 : term344 = term344.
Proof. exact (fun_ext (fun m : nat => @lem4072980 m)). Qed.
Lemma lem4072982 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4072983 : term345 = term345.
Proof. exact (MK_COMB (@lem4072982) (@lem4072981)). Qed.
Lemma lem4072984 (h1 : term264) : term345.
Proof. exact (EQ_MP (@lem4072983) (@lem4071745 h1)). Qed.
Lemma lem4073005 {_102289 _102316 : Type'} (f : _102289 -> _102316) (s : _102289 -> Prop) : (term346 _102289 _102316 f s) = (term346 _102289 _102316 f s).
Proof. exact (eq_refl (term346 _102289 _102316 f s)). Qed.
Lemma lem4073006 {_102289 _102316 : Type'} (f : _102289 -> _102316) : (term348 _102289 _102316 f) = (term348 _102289 _102316 f).
Proof. exact (fun_ext (fun s : _102289 -> Prop => @lem4073005 _102289 _102316 f s)). Qed.
Lemma lem4073007 {_102289 : Type'} : (@all (_102289 -> Prop)) = (@all (_102289 -> Prop)).
Proof. exact (eq_refl (@all (_102289 -> Prop))). Qed.
Lemma lem4073008 {_102289 _102316 : Type'} (f : _102289 -> _102316) : (term349 _102289 _102316 f) = (term349 _102289 _102316 f).
Proof. exact (MK_COMB (@lem4073007 _102289) (@lem4073006 _102289 _102316 f)). Qed.
Lemma lem4073009 {_102289 _102316 : Type'} : (term350 _102289 _102316) = (term350 _102289 _102316).
Proof. exact (fun_ext (fun f : _102289 -> _102316 => @lem4073008 _102289 _102316 f)). Qed.
Lemma lem4073010 {_102289 _102316 : Type'} : (@all (_102289 -> _102316)) = (@all (_102289 -> _102316)).
Proof. exact (eq_refl (@all (_102289 -> _102316))). Qed.
Lemma lem4073011 {_102289 _102316 : Type'} : (term351 _102289 _102316) = (term351 _102289 _102316).
Proof. exact (MK_COMB (@lem4073010 _102289 _102316) (@lem4073009 _102289 _102316)). Qed.
Lemma lem4073012 {_102289 _102316 : Type'} (h1 : term153 _102289 _102316) : term351 _102289 _102316.
Proof. exact (EQ_MP (@lem4073011 _102289 _102316) (@lem4071815 _102289 _102316 h1)). Qed.
Lemma lem4073195 {_102289 _102316 : Type'} (f : _102289 -> _102316) (s : _102289 -> Prop) : (term352 _102289 _102316 f s) = (term352 _102289 _102316 f s).
Proof. exact (eq_refl (term352 _102289 _102316 f s)). Qed.
Lemma lem4073196 {_102289 _102316 : Type'} (f : _102289 -> _102316) : (term354 _102289 _102316 f) = (term354 _102289 _102316 f).
Proof. exact (fun_ext (fun s : _102289 -> Prop => @lem4073195 _102289 _102316 f s)). Qed.
Lemma lem4073197 {_102289 : Type'} : (@all (_102289 -> Prop)) = (@all (_102289 -> Prop)).
Proof. exact (eq_refl (@all (_102289 -> Prop))). Qed.
Lemma lem4073198 {_102289 _102316 : Type'} (f : _102289 -> _102316) : (term355 _102289 _102316 f) = (term355 _102289 _102316 f).
Proof. exact (MK_COMB (@lem4073197 _102289) (@lem4073196 _102289 _102316 f)). Qed.
Lemma lem4073199 {_102289 _102316 : Type'} : (term356 _102289 _102316) = (term356 _102289 _102316).
Proof. exact (fun_ext (fun f : _102289 -> _102316 => @lem4073198 _102289 _102316 f)). Qed.
Lemma lem4073200 {_102289 _102316 : Type'} : (@all (_102289 -> _102316)) = (@all (_102289 -> _102316)).
Proof. exact (eq_refl (@all (_102289 -> _102316))). Qed.
Lemma lem4073201 {_102289 _102316 : Type'} : (term357 _102289 _102316) = (term357 _102289 _102316).
Proof. exact (MK_COMB (@lem4073200 _102289 _102316) (@lem4073199 _102289 _102316)). Qed.
Lemma lem4073202 {_102289 _102316 : Type'} (h1 : term151 _102289 _102316) : term357 _102289 _102316.
Proof. exact (EQ_MP (@lem4073201 _102289 _102316) (@lem4072305 _102289 _102316 h1)). Qed.
Lemma lem4073329 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (t : _102316 -> Prop) : (term294 _102289 _102316 n f s P t) = (term294 _102289 _102316 n f s P t).
Proof. exact (eq_refl (term294 _102289 _102316 n f s P t)). Qed.
Lemma lem4073330 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term302 _102289 _102316 n f s P) = (term302 _102289 _102316 n f s P).
Proof. exact (fun_ext (fun t : _102316 -> Prop => @lem4073329 _102289 _102316 n f s P t)). Qed.
Lemma lem4073331 {_102316 : Type'} : (@all (_102316 -> Prop)) = (@all (_102316 -> Prop)).
Proof. exact (eq_refl (@all (_102316 -> Prop))). Qed.
Lemma lem4073332 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term303 _102289 _102316 n f s P) = (term303 _102289 _102316 n f s P).
Proof. exact (MK_COMB (@lem4073331 _102316) (@lem4073330 _102289 _102316 n f s P)). Qed.
Lemma lem4073365 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term319 _102289 _102316 n s P f t) = (term319 _102289 _102316 n s P f t).
Proof. exact (eq_refl (term319 _102289 _102316 n s P f t)). Qed.
Lemma lem4073366 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term321 _102289 _102316 t n f s P) = (term321 _102289 _102316 t n f s P).
Proof. exact (MK_COMB (@lem4073365 _102289 _102316 n s P f t) (@lem4073332 _102289 _102316 n f s P)). Qed.
Lemma lem4073367 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term321 _102289 _102316 t n f s P) : term321 _102289 _102316 t n f s P.
Proof. exact (EQ_MP (@lem4073366 _102289 _102316 t n f s P) (@lem4072586 _102289 _102316 t n f s P h1)). Qed.
Lemma lem4073368 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term321 _102289 _102316 t n f s P) : term303 _102289 _102316 n f s P.
Proof. exact (proj2 (@lem4073367 _102289 _102316 t n f s P h1)). Qed.
Lemma lem4073369 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term321 _102289 _102316 t n f s P) : term45 _102289 _102316 n s P f t.
Proof. exact (proj1 (@lem4073367 _102289 _102316 t n f s P h1)). Qed.
Lemma lem4073370 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term321 _102289 _102316 t n f s P) : term95 _102289 _102316 n s P f t.
Proof. exact (proj2 (@lem4073369 _102289 _102316 t n f s P h1)). Qed.
Lemma lem4073372 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term321 _102289 _102316 t n f s P) : term90 _102289 _102316 s P f t.
Proof. exact (proj2 (@lem4073370 _102289 _102316 t n f s P h1)). Qed.
Lemma lem4073383 {_102289 _102316 : Type'} (s : _102289 -> Prop) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term325 _102289 _102316 s f t) = (term325 _102289 _102316 s f t).
Proof. exact (eq_refl (term325 _102289 _102316 s f t)). Qed.
Lemma lem4073384 {_102289 _102316 : Type'} (s : _102289 -> Prop) (f : _102289 -> _102316) : (term327 _102289 _102316 s f) = (term327 _102289 _102316 s f).
Proof. exact (fun_ext (fun t : _102289 -> Prop => @lem4073383 _102289 _102316 s f t)). Qed.
Lemma lem4073385 {_102289 : Type'} : (@all (_102289 -> Prop)) = (@all (_102289 -> Prop)).
Proof. exact (eq_refl (@all (_102289 -> Prop))). Qed.
Lemma lem4073386 {_102289 _102316 : Type'} (s : _102289 -> Prop) (f : _102289 -> _102316) : (term328 _102289 _102316 s f) = (term328 _102289 _102316 s f).
Proof. exact (MK_COMB (@lem4073385 _102289) (@lem4073384 _102289 _102316 s f)). Qed.
Lemma lem4073387 {_102289 _102316 : Type'} (f : _102289 -> _102316) : (term329 _102289 _102316 f) = (term329 _102289 _102316 f).
Proof. exact (fun_ext (fun s : _102289 -> Prop => @lem4073386 _102289 _102316 s f)). Qed.
Lemma lem4073388 {_102289 : Type'} : (@all (_102289 -> Prop)) = (@all (_102289 -> Prop)).
Proof. exact (eq_refl (@all (_102289 -> Prop))). Qed.
Lemma lem4073389 {_102289 _102316 : Type'} (f : _102289 -> _102316) : (term330 _102289 _102316 f) = (term330 _102289 _102316 f).
Proof. exact (MK_COMB (@lem4073388 _102289) (@lem4073387 _102289 _102316 f)). Qed.
Lemma lem4073390 {_102289 _102316 : Type'} : (term331 _102289 _102316) = (term331 _102289 _102316).
Proof. exact (fun_ext (fun f : _102289 -> _102316 => @lem4073389 _102289 _102316 f)). Qed.
Lemma lem4073391 {_102289 _102316 : Type'} : (@all (_102289 -> _102316)) = (@all (_102289 -> _102316)).
Proof. exact (eq_refl (@all (_102289 -> _102316))). Qed.
Lemma lem4073393 {_102289 _102316 : Type'} : (term332 _102289 _102316) = (term332 _102289 _102316).
Proof. exact (MK_COMB (@lem4073391 _102289 _102316) (@lem4073390 _102289 _102316)). Qed.
Lemma lem4073394 {_102289 _102316 : Type'} (h1 : term156 _102289 _102316) : term332 _102289 _102316.
Proof. exact (EQ_MP (@lem4073393 _102289 _102316) (@lem4072619 _102289 _102316 h1)). Qed.
Lemma lem4073598 (n : nat) (m : nat) (p : nat) : (term338 n m p) = (term338 n m p).
Proof. exact (eq_refl (term338 n m p)). Qed.
Lemma lem4073599 (n : nat) (m : nat) : (term340 n m) = (term340 n m).
Proof. exact (fun_ext (fun p : nat => @lem4073598 n m p)). Qed.
Lemma lem4073600 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4073601 (n : nat) (m : nat) : (term341 n m) = (term341 n m).
Proof. exact (MK_COMB (@lem4073600) (@lem4073599 n m)). Qed.
Lemma lem4073602 (m : nat) : (term342 m) = (term342 m).
Proof. exact (fun_ext (fun n : nat => @lem4073601 n m)). Qed.
Lemma lem4073603 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4073604 (m : nat) : (term343 m) = (term343 m).
Proof. exact (MK_COMB (@lem4073603) (@lem4073602 m)). Qed.
Lemma lem4073605 : term344 = term344.
Proof. exact (fun_ext (fun m : nat => @lem4073604 m)). Qed.
Lemma lem4073606 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4073608 : term345 = term345.
Proof. exact (MK_COMB (@lem4073606) (@lem4073605)). Qed.
Lemma lem4073609 (h1 : term264) : term345.
Proof. exact (EQ_MP (@lem4073608) (@lem4072984 h1)). Qed.
Lemma lem4073617 {_102289 _102316 : Type'} (f : _102289 -> _102316) (s : _102289 -> Prop) : (term346 _102289 _102316 f s) = (term346 _102289 _102316 f s).
Proof. exact (eq_refl (term346 _102289 _102316 f s)). Qed.
Lemma lem4073618 {_102289 _102316 : Type'} (f : _102289 -> _102316) : (term348 _102289 _102316 f) = (term348 _102289 _102316 f).
Proof. exact (fun_ext (fun s : _102289 -> Prop => @lem4073617 _102289 _102316 f s)). Qed.
Lemma lem4073619 {_102289 : Type'} : (@all (_102289 -> Prop)) = (@all (_102289 -> Prop)).
Proof. exact (eq_refl (@all (_102289 -> Prop))). Qed.
Lemma lem4073620 {_102289 _102316 : Type'} (f : _102289 -> _102316) : (term349 _102289 _102316 f) = (term349 _102289 _102316 f).
Proof. exact (MK_COMB (@lem4073619 _102289) (@lem4073618 _102289 _102316 f)). Qed.
Lemma lem4073621 {_102289 _102316 : Type'} : (term350 _102289 _102316) = (term350 _102289 _102316).
Proof. exact (fun_ext (fun f : _102289 -> _102316 => @lem4073620 _102289 _102316 f)). Qed.
Lemma lem4073622 {_102289 _102316 : Type'} : (@all (_102289 -> _102316)) = (@all (_102289 -> _102316)).
Proof. exact (eq_refl (@all (_102289 -> _102316))). Qed.
Lemma lem4073624 {_102289 _102316 : Type'} : (term351 _102289 _102316) = (term351 _102289 _102316).
Proof. exact (MK_COMB (@lem4073622 _102289 _102316) (@lem4073621 _102289 _102316)). Qed.
Lemma lem4073625 {_102289 _102316 : Type'} (h1 : term153 _102289 _102316) : term351 _102289 _102316.
Proof. exact (EQ_MP (@lem4073624 _102289 _102316) (@lem4073012 _102289 _102316 h1)). Qed.
Lemma lem4073729 {_102289 _102316 : Type'} (f : _102289 -> _102316) (s : _102289 -> Prop) : (term352 _102289 _102316 f s) = (term352 _102289 _102316 f s).
Proof. exact (eq_refl (term352 _102289 _102316 f s)). Qed.
Lemma lem4073730 {_102289 _102316 : Type'} (f : _102289 -> _102316) : (term354 _102289 _102316 f) = (term354 _102289 _102316 f).
Proof. exact (fun_ext (fun s : _102289 -> Prop => @lem4073729 _102289 _102316 f s)). Qed.
Lemma lem4073731 {_102289 : Type'} : (@all (_102289 -> Prop)) = (@all (_102289 -> Prop)).
Proof. exact (eq_refl (@all (_102289 -> Prop))). Qed.
Lemma lem4073732 {_102289 _102316 : Type'} (f : _102289 -> _102316) : (term355 _102289 _102316 f) = (term355 _102289 _102316 f).
Proof. exact (MK_COMB (@lem4073731 _102289) (@lem4073730 _102289 _102316 f)). Qed.
Lemma lem4073733 {_102289 _102316 : Type'} : (term356 _102289 _102316) = (term356 _102289 _102316).
Proof. exact (fun_ext (fun f : _102289 -> _102316 => @lem4073732 _102289 _102316 f)). Qed.
Lemma lem4073734 {_102289 _102316 : Type'} : (@all (_102289 -> _102316)) = (@all (_102289 -> _102316)).
Proof. exact (eq_refl (@all (_102289 -> _102316))). Qed.
Lemma lem4073736 {_102289 _102316 : Type'} : (term357 _102289 _102316) = (term357 _102289 _102316).
Proof. exact (MK_COMB (@lem4073734 _102289 _102316) (@lem4073733 _102289 _102316)). Qed.
Lemma lem4073737 {_102289 _102316 : Type'} (h1 : term151 _102289 _102316) : term357 _102289 _102316.
Proof. exact (EQ_MP (@lem4073736 _102289 _102316) (@lem4073202 _102289 _102316 h1)). Qed.
Lemma lem4073821 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (t : _102316 -> Prop) : (term294 _102289 _102316 n f s P t) = (term294 _102289 _102316 n f s P t).
Proof. exact (eq_refl (term294 _102289 _102316 n f s P t)). Qed.
Lemma lem4073822 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term302 _102289 _102316 n f s P) = (term302 _102289 _102316 n f s P).
Proof. exact (fun_ext (fun t : _102316 -> Prop => @lem4073821 _102289 _102316 n f s P t)). Qed.
Lemma lem4073823 {_102316 : Type'} : (@all (_102316 -> Prop)) = (@all (_102316 -> Prop)).
Proof. exact (eq_refl (@all (_102316 -> Prop))). Qed.
Lemma lem4073825 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term303 _102289 _102316 n f s P) = (term303 _102289 _102316 n f s P).
Proof. exact (MK_COMB (@lem4073823 _102316) (@lem4073822 _102289 _102316 n f s P)). Qed.
Lemma lem4073826 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term321 _102289 _102316 t n f s P) : term303 _102289 _102316 n f s P.
Proof. exact (EQ_MP (@lem4073825 _102289 _102316 n f s P) (@lem4073368 _102289 _102316 t n f s P h1)). Qed.
Lemma lem4073843 {_102289 _102316 : Type'} (_47804 : _102289 -> _102316) (h1 : term156 _102289 _102316) : term358 _102289 _102316 _47804.
Proof. exact (@lem4073394 _102289 _102316 h1 _47804). Qed.
Lemma lem4073844 {_102289 _102316 : Type'} (_47804 : _102289 -> _102316) : (term358 _102289 _102316 _47804) = (term330 _102289 _102316 _47804).
Proof. exact (eq_refl (term358 _102289 _102316 _47804)). Qed.
Lemma lem4073845 {_102289 _102316 : Type'} (_47804 : _102289 -> _102316) (h1 : term156 _102289 _102316) : term330 _102289 _102316 _47804.
Proof. exact (EQ_MP (@lem4073844 _102289 _102316 _47804) (@lem4073843 _102289 _102316 _47804 h1)). Qed.
Lemma lem4073846 {_102289 _102316 : Type'} (_47804 : _102289 -> _102316) (_47805 : _102289 -> Prop) (h1 : term156 _102289 _102316) : term359 _102289 _102316 _47804 _47805.
Proof. exact (@lem4073845 _102289 _102316 _47804 h1 _47805). Qed.
Lemma lem4073847 {_102289 _102316 : Type'} (_47805 : _102289 -> Prop) (_47804 : _102289 -> _102316) : (term359 _102289 _102316 _47804 _47805) = (term328 _102289 _102316 _47805 _47804).
Proof. exact (eq_refl (term359 _102289 _102316 _47804 _47805)). Qed.
Lemma lem4073848 {_102289 _102316 : Type'} (_47805 : _102289 -> Prop) (_47804 : _102289 -> _102316) (h1 : term156 _102289 _102316) : term328 _102289 _102316 _47805 _47804.
Proof. exact (EQ_MP (@lem4073847 _102289 _102316 _47805 _47804) (@lem4073846 _102289 _102316 _47804 _47805 h1)). Qed.
Lemma lem4073849 {_102289 _102316 : Type'} (_47805 : _102289 -> Prop) (_47804 : _102289 -> _102316) (_47806 : _102289 -> Prop) (h1 : term156 _102289 _102316) : term360 _102289 _102316 _47805 _47804 _47806.
Proof. exact (@lem4073848 _102289 _102316 _47805 _47804 h1 _47806). Qed.
Lemma lem4073850 {_102289 _102316 : Type'} (_47805 : _102289 -> Prop) (_47804 : _102289 -> _102316) (_47806 : _102289 -> Prop) : (term360 _102289 _102316 _47805 _47804 _47806) = (term325 _102289 _102316 _47805 _47804 _47806).
Proof. exact (eq_refl (term360 _102289 _102316 _47805 _47804 _47806)). Qed.
Lemma lem4073942 (_47837 : nat) (h1 : term264) : term361 _47837.
Proof. exact (@lem4073609 h1 _47837). Qed.
Lemma lem4073943 (_47837 : nat) : (term361 _47837) = (term343 _47837).
Proof. exact (eq_refl (term361 _47837)). Qed.
Lemma lem4073944 (_47837 : nat) (h1 : term264) : term343 _47837.
Proof. exact (EQ_MP (@lem4073943 _47837) (@lem4073942 _47837 h1)). Qed.
Lemma lem4073945 (_47837 : nat) (_47838 : nat) (h1 : term264) : term362 _47837 _47838.
Proof. exact (@lem4073944 _47837 h1 _47838). Qed.
Lemma lem4073946 (_47838 : nat) (_47837 : nat) : (term362 _47837 _47838) = (term341 _47838 _47837).
Proof. exact (eq_refl (term362 _47837 _47838)). Qed.
Lemma lem4073947 (_47838 : nat) (_47837 : nat) (h1 : term264) : term341 _47838 _47837.
Proof. exact (EQ_MP (@lem4073946 _47838 _47837) (@lem4073945 _47837 _47838 h1)). Qed.
Lemma lem4073948 (_47838 : nat) (_47837 : nat) (_47839 : nat) (h1 : term264) : term363 _47838 _47837 _47839.
Proof. exact (@lem4073947 _47838 _47837 h1 _47839). Qed.
Lemma lem4073949 (_47838 : nat) (_47837 : nat) (_47839 : nat) : (term363 _47838 _47837 _47839) = (term338 _47838 _47837 _47839).
Proof. exact (eq_refl (term363 _47838 _47837 _47839)). Qed.
Lemma lem4073950 (_47838 : nat) (_47837 : nat) (_47839 : nat) (h1 : term264) : term338 _47838 _47837 _47839.
Proof. exact (EQ_MP (@lem4073949 _47838 _47837 _47839) (@lem4073948 _47838 _47837 _47839 h1)). Qed.
Lemma lem4073951 {_102289 _102316 : Type'} (_47840 : _102289 -> _102316) (h1 : term153 _102289 _102316) : term364 _102289 _102316 _47840.
Proof. exact (@lem4073625 _102289 _102316 h1 _47840). Qed.
Lemma lem4073952 {_102289 _102316 : Type'} (_47840 : _102289 -> _102316) : (term364 _102289 _102316 _47840) = (term349 _102289 _102316 _47840).
Proof. exact (eq_refl (term364 _102289 _102316 _47840)). Qed.
Lemma lem4073953 {_102289 _102316 : Type'} (_47840 : _102289 -> _102316) (h1 : term153 _102289 _102316) : term349 _102289 _102316 _47840.
Proof. exact (EQ_MP (@lem4073952 _102289 _102316 _47840) (@lem4073951 _102289 _102316 _47840 h1)). Qed.
Lemma lem4073954 {_102289 _102316 : Type'} (_47840 : _102289 -> _102316) (_47841 : _102289 -> Prop) (h1 : term153 _102289 _102316) : term365 _102289 _102316 _47840 _47841.
Proof. exact (@lem4073953 _102289 _102316 _47840 h1 _47841). Qed.
Lemma lem4073955 {_102289 _102316 : Type'} (_47840 : _102289 -> _102316) (_47841 : _102289 -> Prop) : (term365 _102289 _102316 _47840 _47841) = (term346 _102289 _102316 _47840 _47841).
Proof. exact (eq_refl (term365 _102289 _102316 _47840 _47841)). Qed.
Lemma lem4073993 {_102289 _102316 : Type'} (_47854 : _102289 -> _102316) (h1 : term151 _102289 _102316) : term366 _102289 _102316 _47854.
Proof. exact (@lem4073737 _102289 _102316 h1 _47854). Qed.
Lemma lem4073994 {_102289 _102316 : Type'} (_47854 : _102289 -> _102316) : (term366 _102289 _102316 _47854) = (term355 _102289 _102316 _47854).
Proof. exact (eq_refl (term366 _102289 _102316 _47854)). Qed.
Lemma lem4073995 {_102289 _102316 : Type'} (_47854 : _102289 -> _102316) (h1 : term151 _102289 _102316) : term355 _102289 _102316 _47854.
Proof. exact (EQ_MP (@lem4073994 _102289 _102316 _47854) (@lem4073993 _102289 _102316 _47854 h1)). Qed.
Lemma lem4073996 {_102289 _102316 : Type'} (_47854 : _102289 -> _102316) (_47855 : _102289 -> Prop) (h1 : term151 _102289 _102316) : term367 _102289 _102316 _47854 _47855.
Proof. exact (@lem4073995 _102289 _102316 _47854 h1 _47855). Qed.
Lemma lem4073997 {_102289 _102316 : Type'} (_47854 : _102289 -> _102316) (_47855 : _102289 -> Prop) : (term367 _102289 _102316 _47854 _47855) = (term352 _102289 _102316 _47854 _47855).
Proof. exact (eq_refl (term367 _102289 _102316 _47854 _47855)). Qed.
Lemma lem4074023 {_102289 _102316 : Type'} (_47864 : _102316 -> Prop) (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term321 _102289 _102316 t n f s P) : term368 _102289 _102316 n f s P _47864.
Proof. exact (@lem4073826 _102289 _102316 t n f s P h1 _47864). Qed.
Lemma lem4074024 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (_47864 : _102316 -> Prop) : (term368 _102289 _102316 n f s P _47864) = (term294 _102289 _102316 n f s P _47864).
Proof. exact (eq_refl (term368 _102289 _102316 n f s P _47864)). Qed.
Lemma lem4074031 {_102289 _102316 : Type'} (_47805 : _102289 -> Prop) (_47804 : _102289 -> _102316) (_47806 : _102289 -> Prop) (h1 : term156 _102289 _102316) : term325 _102289 _102316 _47805 _47804 _47806.
Proof. exact (EQ_MP (@lem4073850 _102289 _102316 _47805 _47804 _47806) (@lem4073849 _102289 _102316 _47805 _47804 _47806 h1)). Qed.
Lemma lem4074102 (_47838 : nat) (_47837 : nat) (_47839 : nat) : (term338 _47838 _47837 _47839) = (term369 _47838 _47837 _47839).
Proof. exact (@lem4067929 (term370 _47837 _47838) (term371 _47838 _47839) (Peano.lt _47837 _47839)). Qed.
Lemma lem4074103 (_47838 : nat) (_47837 : nat) (_47839 : nat) (h1 : term264) : term369 _47838 _47837 _47839.
Proof. exact (EQ_MP (@lem4074102 _47838 _47837 _47839) (@lem4073950 _47838 _47837 _47839 h1)). Qed.
Lemma lem4074109 {_102289 _102316 : Type'} (_47840 : _102289 -> _102316) (_47841 : _102289 -> Prop) (h1 : term153 _102289 _102316) : term346 _102289 _102316 _47840 _47841.
Proof. exact (EQ_MP (@lem4073955 _102289 _102316 _47840 _47841) (@lem4073954 _102289 _102316 _47840 _47841 h1)). Qed.
Lemma lem4074151 {_102289 _102316 : Type'} (_47854 : _102289 -> _102316) (_47855 : _102289 -> Prop) (h1 : term151 _102289 _102316) : term352 _102289 _102316 _47854 _47855.
Proof. exact (EQ_MP (@lem4073997 _102289 _102316 _47854 _47855) (@lem4073996 _102289 _102316 _47854 _47855 h1)). Qed.
Lemma lem4074189 {_102289 _102316 : Type'} (_47864 : _102316 -> Prop) (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term321 _102289 _102316 t n f s P) : term294 _102289 _102316 n f s P _47864.
Proof. exact (EQ_MP (@lem4074024 _102289 _102316 n f s P _47864) (@lem4074023 _102289 _102316 _47864 t n f s P h1)). Qed.
Lemma lem4074199 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term321 _102289 _102316 t n f s P) : @FINITE _102289 t.
Proof. exact (proj1 (@lem4073369 _102289 _102316 t n f s P h1)). Qed.
Lemma lem4074200 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term321 _102289 _102316 t n f s P) : term131 _102289 t.
Proof. exact (fun h0 : term132 _102289 t => @lem4074199 _102289 _102316 t n f s P h1). Qed.
Lemma lem4074202 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4074203 {_102289 : Type'} (t : _102289 -> Prop) : (term131 _102289 t) = (@FINITE _102289 t).
Proof. exact (@lem4074202 (@FINITE _102289 t)). Qed.
Lemma lem4074204 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term321 _102289 _102316 t n f s P) : @FINITE _102289 t.
Proof. exact (EQ_MP (@lem4074203 _102289 t) (@lem4074200 _102289 _102316 t n f s P h1)). Qed.
Lemma lem4074210 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4074211 {_102289 _102316 : Type'} (_47854 : _102289 -> _102316) (_47855 : _102289 -> Prop) : (term352 _102289 _102316 _47854 _47855) = (term372 _102289 _102316 _47854 _47855).
Proof. exact (@lem4074210 (term353 _102289 _102316 _47854 _47855) (term132 _102289 _47855)). Qed.
Lemma lem4074217 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4074218 {_102289 _102316 : Type'} (_47854 : _102289 -> _102316) (_47855 : _102289 -> Prop) : (term373 _102289 _102316 _47854 _47855) = (term374 _102289 _102316 _47854 _47855).
Proof. exact (MK_COMB (@lem4074217) (@lem4074211 _102289 _102316 _47854 _47855)). Qed.
Lemma lem4074224 {_102289 _102316 : Type'} (_47854 : _102289 -> _102316) (_47855 : _102289 -> Prop) : (term372 _102289 _102316 _47854 _47855) = (term372 _102289 _102316 _47854 _47855).
Proof. exact (eq_refl (term372 _102289 _102316 _47854 _47855)). Qed.
Lemma lem4074225 {_102289 _102316 : Type'} (_47854 : _102289 -> _102316) (_47855 : _102289 -> Prop) : ((term352 _102289 _102316 _47854 _47855) = (term372 _102289 _102316 _47854 _47855)) = ((term372 _102289 _102316 _47854 _47855) = (term372 _102289 _102316 _47854 _47855)).
Proof. exact (MK_COMB (@lem4074218 _102289 _102316 _47854 _47855) (@lem4074224 _102289 _102316 _47854 _47855)). Qed.
Lemma lem4074227 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4074228 (x : Prop) : (x = x) = True.
Proof. exact (@lem4074227 Prop x). Qed.
Lemma lem4074229 {_102289 _102316 : Type'} (_47854 : _102289 -> _102316) (_47855 : _102289 -> Prop) : ((term372 _102289 _102316 _47854 _47855) = (term372 _102289 _102316 _47854 _47855)) = True.
Proof. exact (@lem4074228 (term372 _102289 _102316 _47854 _47855)). Qed.
Lemma lem4074230 {_102289 _102316 : Type'} (_47854 : _102289 -> _102316) (_47855 : _102289 -> Prop) : ((term352 _102289 _102316 _47854 _47855) = (term372 _102289 _102316 _47854 _47855)) = True.
Proof. exact (TRANS (@lem4074225 _102289 _102316 _47854 _47855) (@lem4074229 _102289 _102316 _47854 _47855)). Qed.
Lemma lem4074231 {_102289 _102316 : Type'} (_47854 : _102289 -> _102316) (_47855 : _102289 -> Prop) : True = ((term352 _102289 _102316 _47854 _47855) = (term372 _102289 _102316 _47854 _47855)).
Proof. exact (SYM (@lem4074230 _102289 _102316 _47854 _47855)). Qed.
Lemma lem4074232 {_102289 _102316 : Type'} (_47854 : _102289 -> _102316) (_47855 : _102289 -> Prop) : (term352 _102289 _102316 _47854 _47855) = (term372 _102289 _102316 _47854 _47855).
Proof. exact (EQ_MP (@lem4074231 _102289 _102316 _47854 _47855) (@lem0)). Qed.
Lemma lem4074233 {_102289 _102316 : Type'} (_47854 : _102289 -> _102316) (_47855 : _102289 -> Prop) (h1 : term151 _102289 _102316) : term372 _102289 _102316 _47854 _47855.
Proof. exact (EQ_MP (@lem4074232 _102289 _102316 _47854 _47855) (@lem4074151 _102289 _102316 _47854 _47855 h1)). Qed.
Lemma lem4074235 (b : Prop) (a : Prop) : (a \/ b) = (term375 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4074236 {_102289 _102316 : Type'} (_47854 : _102289 -> _102316) (_47855 : _102289 -> Prop) : (term372 _102289 _102316 _47854 _47855) = (term376 _102289 _102316 _47854 _47855).
Proof. exact (@lem4074235 (term132 _102289 _47855) (term353 _102289 _102316 _47854 _47855)). Qed.
Lemma lem4074238 (a : Prop) : (term28 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4074239 {_102289 : Type'} (_47855 : _102289 -> Prop) : (term377 _102289 _47855) = (@FINITE _102289 _47855).
Proof. exact (@lem4074238 (@FINITE _102289 _47855)). Qed.
Lemma lem4074240 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4074241 {_102289 : Type'} (_47855 : _102289 -> Prop) : (term378 _102289 _47855) = (term379 _102289 _47855).
Proof. exact (MK_COMB (@lem4074240) (@lem4074239 _102289 _47855)). Qed.
Lemma lem4074242 {_102289 _102316 : Type'} (_47854 : _102289 -> _102316) (_47855 : _102289 -> Prop) : (term353 _102289 _102316 _47854 _47855) = (term353 _102289 _102316 _47854 _47855).
Proof. exact (eq_refl (term353 _102289 _102316 _47854 _47855)). Qed.
Lemma lem4074243 {_102289 _102316 : Type'} (_47854 : _102289 -> _102316) (_47855 : _102289 -> Prop) : (term376 _102289 _102316 _47854 _47855) = (term242 _102289 _102316 _47854 _47855).
Proof. exact (MK_COMB (@lem4074241 _102289 _47855) (@lem4074242 _102289 _102316 _47854 _47855)). Qed.
Lemma lem4074244 {_102289 _102316 : Type'} (_47854 : _102289 -> _102316) (_47855 : _102289 -> Prop) : (term372 _102289 _102316 _47854 _47855) = (term242 _102289 _102316 _47854 _47855).
Proof. exact (TRANS (@lem4074236 _102289 _102316 _47854 _47855) (@lem4074243 _102289 _102316 _47854 _47855)). Qed.
Lemma lem4074247 {_102289 _102316 : Type'} (_47854 : _102289 -> _102316) (_47855 : _102289 -> Prop) (h1 : term151 _102289 _102316) : term242 _102289 _102316 _47854 _47855.
Proof. exact (EQ_MP (@lem4074244 _102289 _102316 _47854 _47855) (@lem4074233 _102289 _102316 _47854 _47855 h1)). Qed.
Lemma lem4074248 {_102289 _102316 : Type'} (_47854 : _102289 -> _102316) (_47855 : _102289 -> Prop) (h1 : term151 _102289 _102316) : term242 _102289 _102316 _47854 _47855.
Proof. exact (@lem4074247 _102289 _102316 _47854 _47855 h1). Qed.
Lemma lem4074249 {_102289 _102316 : Type'} (_47854 : _102289 -> _102316) (t : _102289 -> Prop) (h1 : term151 _102289 _102316) : term242 _102289 _102316 _47854 t.
Proof. exact (@lem4074248 _102289 _102316 _47854 t h1). Qed.
Lemma lem4074252 {_102289 _102316 : Type'} (_47854 : _102289 -> _102316) (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term151 _102289 _102316) (h2 : term321 _102289 _102316 t n f s P) : term353 _102289 _102316 _47854 t.
Proof. exact (@lem4074249 _102289 _102316 _47854 t h1 (@lem4074204 _102289 _102316 t n f s P h2)). Qed.
Lemma lem4074253 {_102289 _102316 : Type'} (_47854 : _102289 -> _102316) (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term151 _102289 _102316) (h2 : term321 _102289 _102316 t n f s P) : term353 _102289 _102316 _47854 t.
Proof. exact (@lem4074252 _102289 _102316 _47854 t n f s P h1 h2). Qed.
Lemma lem4074254 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term151 _102289 _102316) (h2 : term321 _102289 _102316 t n f s P) : term353 _102289 _102316 f t.
Proof. exact (@lem4074253 _102289 _102316 f t n f s P h1 h2). Qed.
Lemma lem4074255 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term151 _102289 _102316) (h2 : term321 _102289 _102316 t n f s P) : term380 _102289 _102316 f t.
Proof. exact (fun h0 : term381 _102289 _102316 f t => @lem4074254 _102289 _102316 t n f s P h1 h2). Qed.
Lemma lem4074257 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4074258 {_102289 _102316 : Type'} (f : _102289 -> _102316) (t : _102289 -> Prop) : (term380 _102289 _102316 f t) = (term353 _102289 _102316 f t).
Proof. exact (@lem4074257 (term353 _102289 _102316 f t)). Qed.
Lemma lem4074259 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term151 _102289 _102316) (h2 : term321 _102289 _102316 t n f s P) : term353 _102289 _102316 f t.
Proof. exact (EQ_MP (@lem4074258 _102289 _102316 f t) (@lem4074255 _102289 _102316 t n f s P h1 h2)). Qed.
Lemma lem4074261 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term321 _102289 _102316 t n f s P) : @FINITE _102289 t.
Proof. exact (proj1 (@lem4073369 _102289 _102316 t n f s P h1)). Qed.
Lemma lem4074262 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term321 _102289 _102316 t n f s P) : term131 _102289 t.
Proof. exact (fun h0 : term132 _102289 t => @lem4074261 _102289 _102316 t n f s P h1). Qed.
Lemma lem4074264 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4074265 {_102289 : Type'} (t : _102289 -> Prop) : (term131 _102289 t) = (@FINITE _102289 t).
Proof. exact (@lem4074264 (@FINITE _102289 t)). Qed.
Lemma lem4074266 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term321 _102289 _102316 t n f s P) : @FINITE _102289 t.
Proof. exact (EQ_MP (@lem4074265 _102289 t) (@lem4074262 _102289 _102316 t n f s P h1)). Qed.
Lemma lem4074272 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4074273 {_102289 _102316 : Type'} (_47840 : _102289 -> _102316) (_47841 : _102289 -> Prop) : (term346 _102289 _102316 _47840 _47841) = (term382 _102289 _102316 _47840 _47841).
Proof. exact (@lem4074272 (term347 _102289 _102316 _47840 _47841) (term132 _102289 _47841)). Qed.
Lemma lem4074279 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4074280 {_102289 _102316 : Type'} (_47840 : _102289 -> _102316) (_47841 : _102289 -> Prop) : (term383 _102289 _102316 _47840 _47841) = (term384 _102289 _102316 _47840 _47841).
Proof. exact (MK_COMB (@lem4074279) (@lem4074273 _102289 _102316 _47840 _47841)). Qed.
Lemma lem4074286 {_102289 _102316 : Type'} (_47840 : _102289 -> _102316) (_47841 : _102289 -> Prop) : (term382 _102289 _102316 _47840 _47841) = (term382 _102289 _102316 _47840 _47841).
Proof. exact (eq_refl (term382 _102289 _102316 _47840 _47841)). Qed.
Lemma lem4074287 {_102289 _102316 : Type'} (_47840 : _102289 -> _102316) (_47841 : _102289 -> Prop) : ((term346 _102289 _102316 _47840 _47841) = (term382 _102289 _102316 _47840 _47841)) = ((term382 _102289 _102316 _47840 _47841) = (term382 _102289 _102316 _47840 _47841)).
Proof. exact (MK_COMB (@lem4074280 _102289 _102316 _47840 _47841) (@lem4074286 _102289 _102316 _47840 _47841)). Qed.
Lemma lem4074289 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4074290 (x : Prop) : (x = x) = True.
Proof. exact (@lem4074289 Prop x). Qed.
Lemma lem4074291 {_102289 _102316 : Type'} (_47840 : _102289 -> _102316) (_47841 : _102289 -> Prop) : ((term382 _102289 _102316 _47840 _47841) = (term382 _102289 _102316 _47840 _47841)) = True.
Proof. exact (@lem4074290 (term382 _102289 _102316 _47840 _47841)). Qed.
Lemma lem4074292 {_102289 _102316 : Type'} (_47840 : _102289 -> _102316) (_47841 : _102289 -> Prop) : ((term346 _102289 _102316 _47840 _47841) = (term382 _102289 _102316 _47840 _47841)) = True.
Proof. exact (TRANS (@lem4074287 _102289 _102316 _47840 _47841) (@lem4074291 _102289 _102316 _47840 _47841)). Qed.
Lemma lem4074293 {_102289 _102316 : Type'} (_47840 : _102289 -> _102316) (_47841 : _102289 -> Prop) : True = ((term346 _102289 _102316 _47840 _47841) = (term382 _102289 _102316 _47840 _47841)).
Proof. exact (SYM (@lem4074292 _102289 _102316 _47840 _47841)). Qed.
Lemma lem4074294 {_102289 _102316 : Type'} (_47840 : _102289 -> _102316) (_47841 : _102289 -> Prop) : (term346 _102289 _102316 _47840 _47841) = (term382 _102289 _102316 _47840 _47841).
Proof. exact (EQ_MP (@lem4074293 _102289 _102316 _47840 _47841) (@lem0)). Qed.
Lemma lem4074295 {_102289 _102316 : Type'} (_47840 : _102289 -> _102316) (_47841 : _102289 -> Prop) (h1 : term153 _102289 _102316) : term382 _102289 _102316 _47840 _47841.
Proof. exact (EQ_MP (@lem4074294 _102289 _102316 _47840 _47841) (@lem4074109 _102289 _102316 _47840 _47841 h1)). Qed.
Lemma lem4074297 (b : Prop) (a : Prop) : (a \/ b) = (term375 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4074298 {_102289 _102316 : Type'} (_47840 : _102289 -> _102316) (_47841 : _102289 -> Prop) : (term382 _102289 _102316 _47840 _47841) = (term385 _102289 _102316 _47840 _47841).
Proof. exact (@lem4074297 (term132 _102289 _47841) (term347 _102289 _102316 _47840 _47841)). Qed.
Lemma lem4074300 (a : Prop) : (term28 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4074301 {_102289 : Type'} (_47841 : _102289 -> Prop) : (term377 _102289 _47841) = (@FINITE _102289 _47841).
Proof. exact (@lem4074300 (@FINITE _102289 _47841)). Qed.
Lemma lem4074302 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4074303 {_102289 : Type'} (_47841 : _102289 -> Prop) : (term378 _102289 _47841) = (term379 _102289 _47841).
Proof. exact (MK_COMB (@lem4074302) (@lem4074301 _102289 _47841)). Qed.
Lemma lem4074304 {_102289 _102316 : Type'} (_47840 : _102289 -> _102316) (_47841 : _102289 -> Prop) : (term347 _102289 _102316 _47840 _47841) = (term347 _102289 _102316 _47840 _47841).
Proof. exact (eq_refl (term347 _102289 _102316 _47840 _47841)). Qed.
Lemma lem4074305 {_102289 _102316 : Type'} (_47840 : _102289 -> _102316) (_47841 : _102289 -> Prop) : (term385 _102289 _102316 _47840 _47841) = (term250 _102289 _102316 _47840 _47841).
Proof. exact (MK_COMB (@lem4074303 _102289 _47841) (@lem4074304 _102289 _102316 _47840 _47841)). Qed.
Lemma lem4074306 {_102289 _102316 : Type'} (_47840 : _102289 -> _102316) (_47841 : _102289 -> Prop) : (term382 _102289 _102316 _47840 _47841) = (term250 _102289 _102316 _47840 _47841).
Proof. exact (TRANS (@lem4074298 _102289 _102316 _47840 _47841) (@lem4074305 _102289 _102316 _47840 _47841)). Qed.
Lemma lem4074309 {_102289 _102316 : Type'} (_47840 : _102289 -> _102316) (_47841 : _102289 -> Prop) (h1 : term153 _102289 _102316) : term250 _102289 _102316 _47840 _47841.
Proof. exact (EQ_MP (@lem4074306 _102289 _102316 _47840 _47841) (@lem4074295 _102289 _102316 _47840 _47841 h1)). Qed.
Lemma lem4074310 {_102289 _102316 : Type'} (_47840 : _102289 -> _102316) (_47841 : _102289 -> Prop) (h1 : term153 _102289 _102316) : term250 _102289 _102316 _47840 _47841.
Proof. exact (@lem4074309 _102289 _102316 _47840 _47841 h1). Qed.
Lemma lem4074311 {_102289 _102316 : Type'} (_47840 : _102289 -> _102316) (t : _102289 -> Prop) (h1 : term153 _102289 _102316) : term250 _102289 _102316 _47840 t.
Proof. exact (@lem4074310 _102289 _102316 _47840 t h1). Qed.
Lemma lem4074314 {_102289 _102316 : Type'} (_47840 : _102289 -> _102316) (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term153 _102289 _102316) (h2 : term321 _102289 _102316 t n f s P) : term347 _102289 _102316 _47840 t.
Proof. exact (@lem4074311 _102289 _102316 _47840 t h1 (@lem4074266 _102289 _102316 t n f s P h2)). Qed.
Lemma lem4074315 {_102289 _102316 : Type'} (_47840 : _102289 -> _102316) (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term153 _102289 _102316) (h2 : term321 _102289 _102316 t n f s P) : term347 _102289 _102316 _47840 t.
Proof. exact (@lem4074314 _102289 _102316 _47840 t n f s P h1 h2). Qed.
Lemma lem4074316 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term153 _102289 _102316) (h2 : term321 _102289 _102316 t n f s P) : term347 _102289 _102316 f t.
Proof. exact (@lem4074315 _102289 _102316 f t n f s P h1 h2). Qed.
Lemma lem4074317 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term153 _102289 _102316) (h2 : term321 _102289 _102316 t n f s P) : term386 _102289 _102316 f t.
Proof. exact (fun h0 : term387 _102289 _102316 f t => @lem4074316 _102289 _102316 t n f s P h1 h2). Qed.
Lemma lem4074319 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4074320 {_102289 _102316 : Type'} (f : _102289 -> _102316) (t : _102289 -> Prop) : (term386 _102289 _102316 f t) = (term347 _102289 _102316 f t).
Proof. exact (@lem4074319 (term347 _102289 _102316 f t)). Qed.
Lemma lem4074321 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term153 _102289 _102316) (h2 : term321 _102289 _102316 t n f s P) : term347 _102289 _102316 f t.
Proof. exact (EQ_MP (@lem4074320 _102289 _102316 f t) (@lem4074317 _102289 _102316 t n f s P h1 h2)). Qed.
Lemma lem4074323 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term321 _102289 _102316 t n f s P) : term89 _102289 t n.
Proof. exact (proj1 (@lem4073370 _102289 _102316 t n f s P h1)). Qed.
Lemma lem4074324 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term321 _102289 _102316 t n f s P) : term134 _102289 t n.
Proof. exact (fun h0 : term135 _102289 t n => @lem4074323 _102289 _102316 t n f s P h1). Qed.
Lemma lem4074326 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4074327 {_102289 : Type'} (t : _102289 -> Prop) (n : nat) : (term134 _102289 t n) = (term89 _102289 t n).
Proof. exact (@lem4074326 (term89 _102289 t n)). Qed.
Lemma lem4074328 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term321 _102289 _102316 t n f s P) : term89 _102289 t n.
Proof. exact (EQ_MP (@lem4074327 _102289 t n) (@lem4074324 _102289 _102316 t n f s P h1)). Qed.
Lemma lem4074334 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4074335 (_47838 : nat) (_47837 : nat) (_47839 : nat) : (term369 _47838 _47837 _47839) = (term388 _47838 _47837 _47839).
Proof. exact (@lem4074334 (term371 _47838 _47839) (term370 _47837 _47838) (Peano.lt _47837 _47839)). Qed.
Lemma lem4074349 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4074350 (_47839 : nat) (_47837 : nat) (_47838 : nat) : (term389 _47838 _47837 _47839) = (term390 _47839 _47837 _47838).
Proof. exact (@lem4074349 (Peano.lt _47837 _47839) (term370 _47837 _47838)). Qed.
Lemma lem4074356 (_47838 : nat) (_47839 : nat) : (term391 _47838 _47839) = (term391 _47838 _47839).
Proof. exact (eq_refl (term391 _47838 _47839)). Qed.
Lemma lem4074357 (_47839 : nat) (_47837 : nat) (_47838 : nat) : (term388 _47838 _47837 _47839) = (term392 _47839 _47837 _47838).
Proof. exact (MK_COMB (@lem4074356 _47838 _47839) (@lem4074350 _47839 _47837 _47838)). Qed.
Lemma lem4074361 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4074362 (_47839 : nat) (_47837 : nat) (_47838 : nat) : (term392 _47839 _47837 _47838) = (term393 _47839 _47837 _47838).
Proof. exact (@lem4074361 (Peano.lt _47837 _47839) (term371 _47838 _47839) (term370 _47837 _47838)). Qed.
Lemma lem4074378 (_47839 : nat) (_47837 : nat) (_47838 : nat) : (term388 _47838 _47837 _47839) = (term393 _47839 _47837 _47838).
Proof. exact (TRANS (@lem4074357 _47839 _47837 _47838) (@lem4074362 _47839 _47837 _47838)). Qed.
Lemma lem4074379 (_47839 : nat) (_47837 : nat) (_47838 : nat) : (term369 _47838 _47837 _47839) = (term393 _47839 _47837 _47838).
Proof. exact (TRANS (@lem4074335 _47838 _47837 _47839) (@lem4074378 _47839 _47837 _47838)). Qed.
Lemma lem4074380 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4074381 (_47839 : nat) (_47837 : nat) (_47838 : nat) : (term394 _47838 _47837 _47839) = (term395 _47839 _47837 _47838).
Proof. exact (MK_COMB (@lem4074380) (@lem4074379 _47839 _47837 _47838)). Qed.
Lemma lem4074395 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4074396 (_47839 : nat) (_47837 : nat) (_47838 : nat) : (term334 _47837 _47838 _47839) = (term396 _47839 _47837 _47838).
Proof. exact (@lem4074395 (term371 _47838 _47839) (term370 _47837 _47838)). Qed.
Lemma lem4074402 (_47837 : nat) (_47839 : nat) : (term397 _47837 _47839) = (term397 _47837 _47839).
Proof. exact (eq_refl (term397 _47837 _47839)). Qed.
Lemma lem4074403 (_47839 : nat) (_47837 : nat) (_47838 : nat) : (term398 _47837 _47838 _47839) = (term393 _47839 _47837 _47838).
Proof. exact (MK_COMB (@lem4074402 _47837 _47839) (@lem4074396 _47839 _47837 _47838)). Qed.
Lemma lem4074414 (_47839 : nat) (_47837 : nat) (_47838 : nat) : ((term369 _47838 _47837 _47839) = (term398 _47837 _47838 _47839)) = ((term393 _47839 _47837 _47838) = (term393 _47839 _47837 _47838)).
Proof. exact (MK_COMB (@lem4074381 _47839 _47837 _47838) (@lem4074403 _47839 _47837 _47838)). Qed.
Lemma lem4074416 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4074417 (x : Prop) : (x = x) = True.
Proof. exact (@lem4074416 Prop x). Qed.
Lemma lem4074418 (_47839 : nat) (_47837 : nat) (_47838 : nat) : ((term393 _47839 _47837 _47838) = (term393 _47839 _47837 _47838)) = True.
Proof. exact (@lem4074417 (term393 _47839 _47837 _47838)). Qed.
Lemma lem4074419 (_47837 : nat) (_47838 : nat) (_47839 : nat) : ((term369 _47838 _47837 _47839) = (term398 _47837 _47838 _47839)) = True.
Proof. exact (TRANS (@lem4074414 _47839 _47837 _47838) (@lem4074418 _47839 _47837 _47838)). Qed.
Lemma lem4074420 (_47837 : nat) (_47838 : nat) (_47839 : nat) : True = ((term369 _47838 _47837 _47839) = (term398 _47837 _47838 _47839)).
Proof. exact (SYM (@lem4074419 _47837 _47838 _47839)). Qed.
Lemma lem4074421 (_47837 : nat) (_47838 : nat) (_47839 : nat) : (term369 _47838 _47837 _47839) = (term398 _47837 _47838 _47839).
Proof. exact (EQ_MP (@lem4074420 _47837 _47838 _47839) (@lem0)). Qed.
Lemma lem4074422 (_47837 : nat) (_47838 : nat) (_47839 : nat) (h1 : term264) : term398 _47837 _47838 _47839.
Proof. exact (EQ_MP (@lem4074421 _47837 _47838 _47839) (@lem4074103 _47838 _47837 _47839 h1)). Qed.
Lemma lem4074424 (b : Prop) (a : Prop) : (a \/ b) = (term375 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4074425 (_47838 : nat) (_47837 : nat) (_47839 : nat) : (term398 _47837 _47838 _47839) = (term399 _47838 _47837 _47839).
Proof. exact (@lem4074424 (term334 _47837 _47838 _47839) (Peano.lt _47837 _47839)). Qed.
Lemma lem4074427 (a : Prop) (b : Prop) : (term400 a b) = (term401 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4074428 (_47837 : nat) (_47838 : nat) (_47839 : nat) : (term402 _47837 _47838 _47839) = (term403 _47837 _47838 _47839).
Proof. exact (@lem4074427 (term370 _47837 _47838) (term371 _47838 _47839)). Qed.
Lemma lem4074430 (a : Prop) : (term28 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4074431 (_47837 : nat) (_47838 : nat) : (term404 _47837 _47838) = (Peano.le _47837 _47838).
Proof. exact (@lem4074430 (Peano.le _47837 _47838)). Qed.
Lemma lem4074432 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4074433 (_47837 : nat) (_47838 : nat) : (term405 _47837 _47838) = (term406 _47837 _47838).
Proof. exact (MK_COMB (@lem4074432) (@lem4074431 _47837 _47838)). Qed.
Lemma lem4074435 (a : Prop) : (term28 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4074436 (_47838 : nat) (_47839 : nat) : (term407 _47838 _47839) = (Peano.lt _47838 _47839).
Proof. exact (@lem4074435 (Peano.lt _47838 _47839)). Qed.
Lemma lem4074437 (_47837 : nat) (_47838 : nat) (_47839 : nat) : (term403 _47837 _47838 _47839) = (term339 _47837 _47838 _47839).
Proof. exact (MK_COMB (@lem4074433 _47837 _47838) (@lem4074436 _47838 _47839)). Qed.
Lemma lem4074438 (_47837 : nat) (_47838 : nat) (_47839 : nat) : (term402 _47837 _47838 _47839) = (term339 _47837 _47838 _47839).
Proof. exact (TRANS (@lem4074428 _47837 _47838 _47839) (@lem4074437 _47837 _47838 _47839)). Qed.
Lemma lem4074439 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4074440 (_47837 : nat) (_47838 : nat) (_47839 : nat) : (term408 _47837 _47838 _47839) = (term409 _47837 _47838 _47839).
Proof. exact (MK_COMB (@lem4074439) (@lem4074438 _47837 _47838 _47839)). Qed.
Lemma lem4074441 (_47837 : nat) (_47839 : nat) : (Peano.lt _47837 _47839) = (Peano.lt _47837 _47839).
Proof. exact (eq_refl (Peano.lt _47837 _47839)). Qed.
Lemma lem4074442 (_47838 : nat) (_47837 : nat) (_47839 : nat) : (term399 _47838 _47837 _47839) = (term258 _47838 _47837 _47839).
Proof. exact (MK_COMB (@lem4074440 _47837 _47838 _47839) (@lem4074441 _47837 _47839)). Qed.
Lemma lem4074443 (_47838 : nat) (_47837 : nat) (_47839 : nat) : (term398 _47837 _47838 _47839) = (term258 _47838 _47837 _47839).
Proof. exact (TRANS (@lem4074425 _47838 _47837 _47839) (@lem4074442 _47838 _47837 _47839)). Qed.
Lemma lem4074445 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term153 _102289 _102316) (h2 : term321 _102289 _102316 t n f s P) : term410 _102289 _102316 f t n.
Proof. exact (conj (@lem4074321 _102289 _102316 t n f s P h1 h2) (@lem4074328 _102289 _102316 t n f s P h2)). Qed.
Lemma lem4074447 (_47838 : nat) (_47837 : nat) (_47839 : nat) (h1 : term264) : term258 _47838 _47837 _47839.
Proof. exact (EQ_MP (@lem4074443 _47838 _47837 _47839) (@lem4074422 _47837 _47838 _47839 h1)). Qed.
Lemma lem4074448 {_102289 _102316 : Type'} (f : _102289 -> _102316) (t : _102289 -> Prop) (n : nat) (h1 : term264) : term411 _102289 _102316 f t n.
Proof. exact (@lem4074447 (@CARD _102289 t) (term412 _102289 _102316 f t) n h1). Qed.
Lemma lem4074451 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term153 _102289 _102316) (h2 : term264) (h3 : term321 _102289 _102316 t n f s P) : term413 _102289 _102316 f t n.
Proof. exact (@lem4074448 _102289 _102316 f t n h2 (@lem4074445 _102289 _102316 t n f s P h1 h3)). Qed.
Lemma lem4074452 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term153 _102289 _102316) (h2 : term264) (h3 : term321 _102289 _102316 t n f s P) : term414 _102289 _102316 f t n.
Proof. exact (fun h0 : term415 _102289 _102316 f t n => @lem4074451 _102289 _102316 t n f s P h1 h2 h3). Qed.
Lemma lem4074454 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4074455 {_102289 _102316 : Type'} (f : _102289 -> _102316) (t : _102289 -> Prop) (n : nat) : (term414 _102289 _102316 f t n) = (term413 _102289 _102316 f t n).
Proof. exact (@lem4074454 (term413 _102289 _102316 f t n)). Qed.
Lemma lem4074456 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term153 _102289 _102316) (h2 : term264) (h3 : term321 _102289 _102316 t n f s P) : term413 _102289 _102316 f t n.
Proof. exact (EQ_MP (@lem4074455 _102289 _102316 f t n) (@lem4074452 _102289 _102316 t n f s P h1 h2 h3)). Qed.
Lemma lem4074458 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term321 _102289 _102316 t n f s P) : @SUBSET _102289 t s.
Proof. exact (proj1 (@lem4073372 _102289 _102316 t n f s P h1)). Qed.
Lemma lem4074459 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term321 _102289 _102316 t n f s P) : term136 _102289 t s.
Proof. exact (fun h0 : term137 _102289 t s => @lem4074458 _102289 _102316 t n f s P h1). Qed.
Lemma lem4074461 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4074462 {_102289 : Type'} (t : _102289 -> Prop) (s : _102289 -> Prop) : (term136 _102289 t s) = (@SUBSET _102289 t s).
Proof. exact (@lem4074461 (@SUBSET _102289 t s)). Qed.
Lemma lem4074463 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term321 _102289 _102316 t n f s P) : @SUBSET _102289 t s.
Proof. exact (EQ_MP (@lem4074462 _102289 t s) (@lem4074459 _102289 _102316 t n f s P h1)). Qed.
Lemma lem4074469 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4074470 {_102289 _102316 : Type'} (_47804 : _102289 -> _102316) (_47805 : _102289 -> Prop) (_47806 : _102289 -> Prop) : (term325 _102289 _102316 _47805 _47804 _47806) = (term416 _102289 _102316 _47804 _47805 _47806).
Proof. exact (@lem4074469 (term326 _102289 _102316 _47805 _47804 _47806) (term137 _102289 _47805 _47806)). Qed.
Lemma lem4074476 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4074477 {_102289 _102316 : Type'} (_47804 : _102289 -> _102316) (_47805 : _102289 -> Prop) (_47806 : _102289 -> Prop) : (term417 _102289 _102316 _47805 _47804 _47806) = (term418 _102289 _102316 _47804 _47805 _47806).
Proof. exact (MK_COMB (@lem4074476) (@lem4074470 _102289 _102316 _47804 _47805 _47806)). Qed.
Lemma lem4074483 {_102289 _102316 : Type'} (_47804 : _102289 -> _102316) (_47805 : _102289 -> Prop) (_47806 : _102289 -> Prop) : (term416 _102289 _102316 _47804 _47805 _47806) = (term416 _102289 _102316 _47804 _47805 _47806).
Proof. exact (eq_refl (term416 _102289 _102316 _47804 _47805 _47806)). Qed.
Lemma lem4074484 {_102289 _102316 : Type'} (_47804 : _102289 -> _102316) (_47805 : _102289 -> Prop) (_47806 : _102289 -> Prop) : ((term325 _102289 _102316 _47805 _47804 _47806) = (term416 _102289 _102316 _47804 _47805 _47806)) = ((term416 _102289 _102316 _47804 _47805 _47806) = (term416 _102289 _102316 _47804 _47805 _47806)).
Proof. exact (MK_COMB (@lem4074477 _102289 _102316 _47804 _47805 _47806) (@lem4074483 _102289 _102316 _47804 _47805 _47806)). Qed.
Lemma lem4074486 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4074487 (x : Prop) : (x = x) = True.
Proof. exact (@lem4074486 Prop x). Qed.
Lemma lem4074488 {_102289 _102316 : Type'} (_47804 : _102289 -> _102316) (_47805 : _102289 -> Prop) (_47806 : _102289 -> Prop) : ((term416 _102289 _102316 _47804 _47805 _47806) = (term416 _102289 _102316 _47804 _47805 _47806)) = True.
Proof. exact (@lem4074487 (term416 _102289 _102316 _47804 _47805 _47806)). Qed.
Lemma lem4074489 {_102289 _102316 : Type'} (_47804 : _102289 -> _102316) (_47805 : _102289 -> Prop) (_47806 : _102289 -> Prop) : ((term325 _102289 _102316 _47805 _47804 _47806) = (term416 _102289 _102316 _47804 _47805 _47806)) = True.
Proof. exact (TRANS (@lem4074484 _102289 _102316 _47804 _47805 _47806) (@lem4074488 _102289 _102316 _47804 _47805 _47806)). Qed.
Lemma lem4074490 {_102289 _102316 : Type'} (_47804 : _102289 -> _102316) (_47805 : _102289 -> Prop) (_47806 : _102289 -> Prop) : True = ((term325 _102289 _102316 _47805 _47804 _47806) = (term416 _102289 _102316 _47804 _47805 _47806)).
Proof. exact (SYM (@lem4074489 _102289 _102316 _47804 _47805 _47806)). Qed.
Lemma lem4074491 {_102289 _102316 : Type'} (_47804 : _102289 -> _102316) (_47805 : _102289 -> Prop) (_47806 : _102289 -> Prop) : (term325 _102289 _102316 _47805 _47804 _47806) = (term416 _102289 _102316 _47804 _47805 _47806).
Proof. exact (EQ_MP (@lem4074490 _102289 _102316 _47804 _47805 _47806) (@lem0)). Qed.
Lemma lem4074492 {_102289 _102316 : Type'} (_47804 : _102289 -> _102316) (_47805 : _102289 -> Prop) (_47806 : _102289 -> Prop) (h1 : term156 _102289 _102316) : term416 _102289 _102316 _47804 _47805 _47806.
Proof. exact (EQ_MP (@lem4074491 _102289 _102316 _47804 _47805 _47806) (@lem4074031 _102289 _102316 _47805 _47804 _47806 h1)). Qed.
Lemma lem4074494 (b : Prop) (a : Prop) : (a \/ b) = (term375 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4074495 {_102289 _102316 : Type'} (_47805 : _102289 -> Prop) (_47804 : _102289 -> _102316) (_47806 : _102289 -> Prop) : (term416 _102289 _102316 _47804 _47805 _47806) = (term419 _102289 _102316 _47805 _47804 _47806).
Proof. exact (@lem4074494 (term137 _102289 _47805 _47806) (term326 _102289 _102316 _47805 _47804 _47806)). Qed.
Lemma lem4074497 (a : Prop) : (term28 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4074498 {_102289 : Type'} (_47805 : _102289 -> Prop) (_47806 : _102289 -> Prop) : (term420 _102289 _47805 _47806) = (@SUBSET _102289 _47805 _47806).
Proof. exact (@lem4074497 (@SUBSET _102289 _47805 _47806)). Qed.
Lemma lem4074499 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4074500 {_102289 : Type'} (_47805 : _102289 -> Prop) (_47806 : _102289 -> Prop) : (term421 _102289 _47805 _47806) = (term422 _102289 _47805 _47806).
Proof. exact (MK_COMB (@lem4074499) (@lem4074498 _102289 _47805 _47806)). Qed.
Lemma lem4074501 {_102289 _102316 : Type'} (_47805 : _102289 -> Prop) (_47804 : _102289 -> _102316) (_47806 : _102289 -> Prop) : (term326 _102289 _102316 _47805 _47804 _47806) = (term326 _102289 _102316 _47805 _47804 _47806).
Proof. exact (eq_refl (term326 _102289 _102316 _47805 _47804 _47806)). Qed.
Lemma lem4074502 {_102289 _102316 : Type'} (_47805 : _102289 -> Prop) (_47804 : _102289 -> _102316) (_47806 : _102289 -> Prop) : (term419 _102289 _102316 _47805 _47804 _47806) = (term271 _102289 _102316 _47805 _47804 _47806).
Proof. exact (MK_COMB (@lem4074500 _102289 _47805 _47806) (@lem4074501 _102289 _102316 _47805 _47804 _47806)). Qed.
Lemma lem4074503 {_102289 _102316 : Type'} (_47805 : _102289 -> Prop) (_47804 : _102289 -> _102316) (_47806 : _102289 -> Prop) : (term416 _102289 _102316 _47804 _47805 _47806) = (term271 _102289 _102316 _47805 _47804 _47806).
Proof. exact (TRANS (@lem4074495 _102289 _102316 _47805 _47804 _47806) (@lem4074502 _102289 _102316 _47805 _47804 _47806)). Qed.
Lemma lem4074506 {_102289 _102316 : Type'} (_47805 : _102289 -> Prop) (_47804 : _102289 -> _102316) (_47806 : _102289 -> Prop) (h1 : term156 _102289 _102316) : term271 _102289 _102316 _47805 _47804 _47806.
Proof. exact (EQ_MP (@lem4074503 _102289 _102316 _47805 _47804 _47806) (@lem4074492 _102289 _102316 _47804 _47805 _47806 h1)). Qed.
Lemma lem4074507 {_102289 _102316 : Type'} (_47805 : _102289 -> Prop) (_47804 : _102289 -> _102316) (_47806 : _102289 -> Prop) (h1 : term156 _102289 _102316) : term271 _102289 _102316 _47805 _47804 _47806.
Proof. exact (@lem4074506 _102289 _102316 _47805 _47804 _47806 h1). Qed.
Lemma lem4074508 {_102289 _102316 : Type'} (t : _102289 -> Prop) (_47804 : _102289 -> _102316) (s : _102289 -> Prop) (h1 : term156 _102289 _102316) : term271 _102289 _102316 t _47804 s.
Proof. exact (@lem4074507 _102289 _102316 t _47804 s h1). Qed.
Lemma lem4074511 {_102289 _102316 : Type'} (_47804 : _102289 -> _102316) (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term321 _102289 _102316 t n f s P) : term326 _102289 _102316 t _47804 s.
Proof. exact (@lem4074508 _102289 _102316 t _47804 s h1 (@lem4074463 _102289 _102316 t n f s P h2)). Qed.
Lemma lem4074512 {_102289 _102316 : Type'} (_47804 : _102289 -> _102316) (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term321 _102289 _102316 t n f s P) : term326 _102289 _102316 t _47804 s.
Proof. exact (@lem4074511 _102289 _102316 _47804 t n f s P h1 h2). Qed.
Lemma lem4074513 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term321 _102289 _102316 t n f s P) : term326 _102289 _102316 t f s.
Proof. exact (@lem4074512 _102289 _102316 f t n f s P h1 h2). Qed.
Lemma lem4074514 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term321 _102289 _102316 t n f s P) : term423 _102289 _102316 t f s.
Proof. exact (fun h0 : term424 _102289 _102316 t f s => @lem4074513 _102289 _102316 t n f s P h1 h2). Qed.
Lemma lem4074516 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4074517 {_102289 _102316 : Type'} (t : _102289 -> Prop) (f : _102289 -> _102316) (s : _102289 -> Prop) : (term423 _102289 _102316 t f s) = (term326 _102289 _102316 t f s).
Proof. exact (@lem4074516 (term326 _102289 _102316 t f s)). Qed.
Lemma lem4074518 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term321 _102289 _102316 t n f s P) : term326 _102289 _102316 t f s.
Proof. exact (EQ_MP (@lem4074517 _102289 _102316 t f s) (@lem4074514 _102289 _102316 t n f s P h1 h2)). Qed.
Lemma lem4074520 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term321 _102289 _102316 t n f s P) : term47 _102289 _102316 P f t.
Proof. exact (proj2 (@lem4073372 _102289 _102316 t n f s P h1)). Qed.
Lemma lem4074521 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term321 _102289 _102316 t n f s P) : term138 _102289 _102316 P f t.
Proof. exact (fun h0 : term139 _102289 _102316 P f t => @lem4074520 _102289 _102316 t n f s P h1). Qed.
Lemma lem4074523 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4074524 {_102289 _102316 : Type'} (P : type686 _102316) (f : _102289 -> _102316) (t : _102289 -> Prop) : (term138 _102289 _102316 P f t) = (term47 _102289 _102316 P f t).
Proof. exact (@lem4074523 (term47 _102289 _102316 P f t)). Qed.
Lemma lem4074525 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term321 _102289 _102316 t n f s P) : term47 _102289 _102316 P f t.
Proof. exact (EQ_MP (@lem4074524 _102289 _102316 P f t) (@lem4074521 _102289 _102316 t n f s P h1)). Qed.
Lemma lem4074527 (a : Prop) (b : Prop) : (term140 a b) = (term141 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4074528 {_102289 _102316 : Type'} (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (_47864 : _102316 -> Prop) : (term287 _102289 _102316 f s P _47864) = (term286 _102289 _102316 f s P _47864).
Proof. exact (@lem4074527 (term288 _102289 _102316 _47864 f s) (P _47864)). Qed.
Lemma lem4074529 {_102316 : Type'} (_47864 : _102316 -> Prop) (n : nat) : (term85 _102316 _47864 n) = (term85 _102316 _47864 n).
Proof. exact (eq_refl (term85 _102316 _47864 n)). Qed.
Lemma lem4074530 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (_47864 : _102316 -> Prop) : (term290 _102289 _102316 n f s P _47864) = (term289 _102289 _102316 n f s P _47864).
Proof. exact (MK_COMB (@lem4074529 _102316 _47864 n) (@lem4074528 _102289 _102316 f s P _47864)). Qed.
Lemma lem4074532 (a : Prop) (b : Prop) : (term140 a b) = (term141 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4074533 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (_47864 : _102316 -> Prop) : (term289 _102289 _102316 n f s P _47864) = (term291 _102289 _102316 n f s P _47864).
Proof. exact (@lem4074532 (term89 _102316 _47864 n) (term292 _102289 _102316 f s P _47864)). Qed.
Lemma lem4074534 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (_47864 : _102316 -> Prop) : (term290 _102289 _102316 n f s P _47864) = (term291 _102289 _102316 n f s P _47864).
Proof. exact (TRANS (@lem4074530 _102289 _102316 n f s P _47864) (@lem4074533 _102289 _102316 n f s P _47864)). Qed.
Lemma lem4074535 {_102316 : Type'} (_47864 : _102316 -> Prop) : (term91 _102316 _47864) = (term91 _102316 _47864).
Proof. exact (eq_refl (term91 _102316 _47864)). Qed.
Lemma lem4074536 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (_47864 : _102316 -> Prop) : (term294 _102289 _102316 n f s P _47864) = (term293 _102289 _102316 n f s P _47864).
Proof. exact (MK_COMB (@lem4074535 _102316 _47864) (@lem4074534 _102289 _102316 n f s P _47864)). Qed.
Lemma lem4074538 (a : Prop) (b : Prop) : (term140 a b) = (term141 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4074539 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (_47864 : _102316 -> Prop) : (term293 _102289 _102316 n f s P _47864) = (term295 _102289 _102316 n f s P _47864).
Proof. exact (@lem4074538 (@FINITE _102316 _47864) (term296 _102289 _102316 n f s P _47864)). Qed.
Lemma lem4074540 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (_47864 : _102316 -> Prop) : (term294 _102289 _102316 n f s P _47864) = (term295 _102289 _102316 n f s P _47864).
Proof. exact (TRANS (@lem4074536 _102289 _102316 n f s P _47864) (@lem4074539 _102289 _102316 n f s P _47864)). Qed.
Lemma lem4074542 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4074543 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (_47864 : _102316 -> Prop) : (term295 _102289 _102316 n f s P _47864) = (term425 _102289 _102316 n f s P _47864).
Proof. exact (@lem4074542 (term283 _102289 _102316 n f s P _47864)). Qed.
Lemma lem4074544 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (_47864 : _102316 -> Prop) : (term294 _102289 _102316 n f s P _47864) = (term425 _102289 _102316 n f s P _47864).
Proof. exact (TRANS (@lem4074540 _102289 _102316 n f s P _47864) (@lem4074543 _102289 _102316 n f s P _47864)). Qed.
Lemma lem4074546 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term321 _102289 _102316 t n f s P) : term426 _102289 _102316 s P f t.
Proof. exact (conj (@lem4074518 _102289 _102316 t n f s P h1 h2) (@lem4074525 _102289 _102316 t n f s P h2)). Qed.
Lemma lem4074547 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term153 _102289 _102316) (h3 : term264) (h4 : term321 _102289 _102316 t n f s P) : term427 _102289 _102316 n s P f t.
Proof. exact (conj (@lem4074456 _102289 _102316 t n f s P h2 h3 h4) (@lem4074546 _102289 _102316 t n f s P h1 h4)). Qed.
Lemma lem4074548 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term151 _102289 _102316) (h3 : term153 _102289 _102316) (h4 : term264) (h5 : term321 _102289 _102316 t n f s P) : term428 _102289 _102316 n s P f t.
Proof. exact (conj (@lem4074259 _102289 _102316 t n f s P h2 h5) (@lem4074547 _102289 _102316 t n f s P h1 h3 h4 h5)). Qed.
Lemma lem4074550 {_102289 _102316 : Type'} (_47864 : _102316 -> Prop) (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term321 _102289 _102316 t n f s P) : term425 _102289 _102316 n f s P _47864.
Proof. exact (EQ_MP (@lem4074544 _102289 _102316 n f s P _47864) (@lem4074189 _102289 _102316 _47864 t n f s P h1)). Qed.
Lemma lem4074551 {_102289 _102316 : Type'} (_47864 : _102316 -> Prop) (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term321 _102289 _102316 t n f s P) : term425 _102289 _102316 n f s P _47864.
Proof. exact (@lem4074550 _102289 _102316 _47864 t n f s P h1). Qed.
Lemma lem4074552 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term321 _102289 _102316 t n f s P) : term429 _102289 _102316 n s P f t.
Proof. exact (@lem4074551 _102289 _102316 (@IMAGE _102289 _102316 f t) t n f s P h1). Qed.
Lemma lem4074555 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term151 _102289 _102316) (h3 : term153 _102289 _102316) (h4 : term264) (h5 : term321 _102289 _102316 t n f s P) : False.
Proof. exact (@lem4074552 _102289 _102316 t n f s P h5 (@lem4074548 _102289 _102316 t n f s P h1 h2 h3 h4 h5)). Qed.
Lemma lem4074556 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term151 _102289 _102316) (h3 : term153 _102289 _102316) (h4 : term264) (h5 : term321 _102289 _102316 t n f s P) : term143.
Proof. exact (fun h0 : ~ False => @lem4074555 _102289 _102316 t n f s P h1 h2 h3 h4 h5). Qed.
Lemma lem4074558 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4074559 : term143 = False.
Proof. exact (@lem4074558 False). Qed.
Lemma lem4074560 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term151 _102289 _102316) (h3 : term153 _102289 _102316) (h4 : term264) (h5 : term321 _102289 _102316 t n f s P) : False.
Proof. exact (EQ_MP (@lem4074559) (@lem4074556 _102289 _102316 t n f s P h1 h2 h3 h4 h5)). Qed.
Lemma lem4074561 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term151 _102289 _102316) (h3 : term153 _102289 _102316) (h4 : term264) (h5 : term321 _102289 _102316 t n f s P) : (term321 _102289 _102316 t n f s P) = False.
Proof. exact (prop_ext (fun h6 : term321 _102289 _102316 t n f s P => @lem4074560 _102289 _102316 t n f s P h1 h2 h3 h4 h5) (fun h6 : False => @lem4073367 _102289 _102316 t n f s P h5)). Qed.
Lemma lem4074562 {_102289 _102316 : Type'} (t : _102289 -> Prop) (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term151 _102289 _102316) (h3 : term153 _102289 _102316) (h4 : term264) (h5 : term321 _102289 _102316 t n f s P) : False.
Proof. exact (EQ_MP (@lem4074561 _102289 _102316 t n f s P h1 h2 h3 h4 h5) (@lem4073367 _102289 _102316 t n f s P h5)). Qed.
Lemma lem4074563 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term151 _102289 _102316) (h3 : term153 _102289 _102316) (h4 : term264) (h5 : term150 _102289 _102316 n f s P) : False.
Proof. exact (ex_elim (@lem4070815 _102289 _102316 n f s P h5) (fun t : _102289 -> Prop => fun h0 : term323 _102289 _102316 n f s P t => @lem4074562 _102289 _102316 t n f s P h1 h2 h3 h4 h0)). Qed.
Lemma lem4074564 {_102289 _102316 A : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term151 _102289 _102316) (h3 : term153 _102289 _102316) (h4 : term264) (h5 : term150 _102289 _102316 n f s P) : term163 _102316 A.
Proof. exact (fun h0 : term152 _102316 A => @lem4074563 _102289 _102316 n f s P h1 h2 h3 h4 h5). Qed.
Lemma lem4074565 {_102316 A : Type'} : (term163 _102316 A) = (term164 _102316 A).
Proof. exact (@lem69 (term152 _102316 A)). Qed.
Lemma lem4074566 {_102289 _102316 A : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term151 _102289 _102316) (h3 : term153 _102289 _102316) (h4 : term264) (h5 : term150 _102289 _102316 n f s P) : term164 _102316 A.
Proof. exact (EQ_MP (@lem4074565 _102316 A) (@lem4074564 _102289 _102316 A n f s P h1 h2 h3 h4 h5)). Qed.
Lemma lem4074567 {_102289 _102316 A : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term151 _102289 _102316) (h3 : term153 _102289 _102316) (h4 : term264) (h5 : term150 _102289 _102316 n f s P) : term167 _102289 _102316 A.
Proof. exact (fun h0 : term152 _102289 A => @lem4074566 _102289 _102316 A n f s P h1 h2 h3 h4 h5). Qed.
Lemma lem4074568 {_102289 _102316 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term151 _102289 _102316) (h3 : term153 _102289 _102316) (h4 : term264) (h5 : term150 _102289 _102316 n f s P) : term170 _102289 _102316 A B.
Proof. exact (fun h0 : term151 _102316 B => @lem4074567 _102289 _102316 A n f s P h1 h2 h3 h4 h5). Qed.
Lemma lem4074569 {_102289 _102316 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term151 _102289 _102316) (h3 : term153 _102289 _102316) (h4 : term264) (h5 : term150 _102289 _102316 n f s P) : term172 _102289 _102316 A B.
Proof. exact (fun h0 : term151 _102289 B => @lem4074568 _102289 _102316 A B n f s P h1 h2 h3 h4 h5). Qed.
Lemma lem4074570 {_102289 _102316 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term153 _102289 _102316) (h3 : term264) (h4 : term150 _102289 _102316 n f s P) : term174 _102289 _102316 A B.
Proof. exact (fun h0 : term151 _102289 _102316 => @lem4074569 _102289 _102316 A B n f s P h1 h0 h2 h3 h4). Qed.
Lemma lem4074571 {_102289 _102316 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term153 _102289 _102316) (h3 : term264) (h4 : term150 _102289 _102316 n f s P) : term177 _102289 _102316 A B.
Proof. exact (fun h0 : term154 B => @lem4074570 _102289 _102316 A B n f s P h1 h2 h3 h4). Qed.
Lemma lem4074572 {_102289 _102316 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term153 _102289 _102316) (h3 : term264) (h4 : term150 _102289 _102316 n f s P) : term180 _102289 _102316 A B.
Proof. exact (fun h0 : term153 A B => @lem4074571 _102289 _102316 A B n f s P h1 h2 h3 h4). Qed.
Lemma lem4074573 {_102289 _102316 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term153 _102289 _102316) (h3 : term264) (h4 : term150 _102289 _102316 n f s P) : term183 _102289 _102316 A B.
Proof. exact (fun h0 : term155 _102316 A => @lem4074572 _102289 _102316 A B n f s P h1 h2 h3 h4). Qed.
Lemma lem4074574 {_102289 _102316 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term153 _102289 _102316) (h3 : term264) (h4 : term150 _102289 _102316 n f s P) : term185 _102289 _102316 A B.
Proof. exact (fun h0 : term155 _102289 A => @lem4074573 _102289 _102316 A B n f s P h1 h2 h3 h4). Qed.
Lemma lem4074575 {_102289 _102316 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term153 _102289 _102316) (h3 : term264) (h4 : term150 _102289 _102316 n f s P) : term187 _102289 _102316 A B.
Proof. exact (fun h0 : term153 _102316 B => @lem4074574 _102289 _102316 A B n f s P h1 h2 h3 h4). Qed.
Lemma lem4074576 {_102289 _102316 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term153 _102289 _102316) (h3 : term264) (h4 : term150 _102289 _102316 n f s P) : term189 _102289 _102316 A B.
Proof. exact (fun h0 : term153 _102289 B => @lem4074575 _102289 _102316 A B n f s P h1 h2 h3 h4). Qed.
Lemma lem4074577 {_102289 _102316 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term264) (h3 : term150 _102289 _102316 n f s P) : term191 _102289 _102316 A B.
Proof. exact (fun h0 : term153 _102289 _102316 => @lem4074576 _102289 _102316 A B n f s P h1 h0 h2 h3). Qed.
Lemma lem4074578 {_102289 _102316 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term150 _102289 _102316 n f s P) : term194 _102289 _102316 A B.
Proof. exact (fun h0 : term264 => @lem4074577 _102289 _102316 A B n f s P h1 h0 h2). Qed.
Lemma lem4074579 {_102289 _102316 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term150 _102289 _102316 n f s P) : term197 _102289 _102316 A B.
Proof. exact (fun h0 : term158 B => @lem4074578 _102289 _102316 A B n f s P h1 h2). Qed.
Lemma lem4074580 {_102289 _102316 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term150 _102289 _102316 n f s P) : term200 _102289 _102316 A B.
Proof. exact (fun h0 : term156 A B => @lem4074579 _102289 _102316 A B n f s P h1 h2). Qed.
Lemma lem4074581 {_102289 _102316 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term150 _102289 _102316 n f s P) : term203 _102289 _102316 A B.
Proof. exact (fun h0 : term157 _102316 A => @lem4074580 _102289 _102316 A B n f s P h1 h2). Qed.
Lemma lem4074582 {_102289 _102316 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term150 _102289 _102316 n f s P) : term205 _102289 _102316 A B.
Proof. exact (fun h0 : term157 _102289 A => @lem4074581 _102289 _102316 A B n f s P h1 h2). Qed.
Lemma lem4074583 {_102289 _102316 _87593 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term150 _102289 _102316 n f s P) : term207 _102289 _102316 _87593 A B.
Proof. exact (fun h0 : term157 _102316 _87593 => @lem4074582 _102289 _102316 A B n f s P h1 h2). Qed.
Lemma lem4074584 {_102289 _102316 _87593 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term150 _102289 _102316 n f s P) : term209 _102289 _102316 _87593 A B.
Proof. exact (fun h0 : term157 _102289 _87593 => @lem4074583 _102289 _102316 _87593 A B n f s P h1 h2). Qed.
Lemma lem4074585 {_102289 _102316 _87593 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term150 _102289 _102316 n f s P) : term211 _102289 _102316 _87593 A B.
Proof. exact (fun h0 : term156 _102316 B => @lem4074584 _102289 _102316 _87593 A B n f s P h1 h2). Qed.
Lemma lem4074586 {_102289 _102316 _87593 _87604 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term150 _102289 _102316 n f s P) : term213 _102289 _102316 _87593 _87604 A B.
Proof. exact (fun h0 : term156 _102316 _87604 => @lem4074585 _102289 _102316 _87593 A B n f s P h1 h2). Qed.
Lemma lem4074587 {_102289 _102316 _87593 _87604 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term150 _102289 _102316 n f s P) : term215 _102289 _102316 _87593 _87604 A B.
Proof. exact (fun h0 : term156 _102289 B => @lem4074586 _102289 _102316 _87593 _87604 A B n f s P h1 h2). Qed.
Lemma lem4074588 {_102289 _102316 _87593 _87604 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term156 _102289 _102316) (h2 : term150 _102289 _102316 n f s P) : term217 _102289 _102316 _87593 _87604 A B.
Proof. exact (fun h0 : term156 _102289 _87604 => @lem4074587 _102289 _102316 _87593 _87604 A B n f s P h1 h2). Qed.
Lemma lem4074589 {_102289 _102316 _87593 _87604 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term150 _102289 _102316 n f s P) : term219 _102289 _102316 _87593 _87604 A B.
Proof. exact (fun h0 : term156 _102289 _102316 => @lem4074588 _102289 _102316 _87593 _87604 A B n f s P h0 h1). Qed.
Lemma lem4074590 {_102289 _102316 _87593 _87604 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : term221 _102289 _102316 _87593 _87604 A B n f s P.
Proof. exact (fun h0 : term150 _102289 _102316 n f s P => @lem4074589 _102289 _102316 _87593 _87604 A B n f s P h0). Qed.
Lemma lem4074595 {_102289 _102316 _87593 _87604 A B : Type'} (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : term225 _102289 _102316 _87593 _87604 A B f s P.
Proof. exact (fun n : nat => @lem4074590 _102289 _102316 _87593 _87604 A B n f s P). Qed.
Lemma lem4074600 {_102289 _102316 _87593 _87604 A B : Type'} (s : _102289 -> Prop) (P : type686 _102316) : term229 _102289 _102316 _87593 _87604 A B s P.
Proof. exact (fun f : _102289 -> _102316 => @lem4074595 _102289 _102316 _87593 _87604 A B f s P). Qed.
Lemma lem4074605 {_102289 _102316 _87593 _87604 A B : Type'} (P : type686 _102316) : term233 _102289 _102316 _87593 _87604 A B P.
Proof. exact (fun s : _102289 -> Prop => @lem4074600 _102289 _102316 _87593 _87604 A B s P). Qed.
Lemma lem4074610 {_102289 _102316 _87593 _87604 A B : Type'} : term237 _102289 _102316 _87593 _87604 A B.
Proof. exact (fun P : type686 _102316 => @lem4074605 _102289 _102316 _87593 _87604 A B P). Qed.
Lemma lem4074611 {_102289 _102316 _87593 _87604 A B : Type'} : term236 _102289 _102316 _87593 _87604 A B.
Proof. exact (EQ_MP (@lem4070636 _102289 _102316 _87593 _87604 A B) (@lem4074610 _102289 _102316 _87593 _87604 A B)). Qed.
Lemma lem4074612 {_102289 _102316 _87593 _87604 A B : Type'} (P : type686 _102316) : term430 _102289 _102316 _87593 _87604 A B P.
Proof. exact (@lem4074611 _102289 _102316 _87593 _87604 A B P). Qed.
Lemma lem4074613 {_102289 _102316 _87593 _87604 A B : Type'} (P : type686 _102316) : (term430 _102289 _102316 _87593 _87604 A B P) = (term232 _102289 _102316 _87593 _87604 A B P).
Proof. exact (eq_refl (term430 _102289 _102316 _87593 _87604 A B P)). Qed.
Lemma lem4074614 {_102289 _102316 _87593 _87604 A B : Type'} (P : type686 _102316) : term232 _102289 _102316 _87593 _87604 A B P.
Proof. exact (EQ_MP (@lem4074613 _102289 _102316 _87593 _87604 A B P) (@lem4074612 _102289 _102316 _87593 _87604 A B P)). Qed.
Lemma lem4074615 {_102289 _102316 _87593 _87604 A B : Type'} (P : type686 _102316) (s : _102289 -> Prop) : term431 _102289 _102316 _87593 _87604 A B P s.
Proof. exact (@lem4074614 _102289 _102316 _87593 _87604 A B P s). Qed.
Lemma lem4074616 {_102289 _102316 _87593 _87604 A B : Type'} (s : _102289 -> Prop) (P : type686 _102316) : (term431 _102289 _102316 _87593 _87604 A B P s) = (term228 _102289 _102316 _87593 _87604 A B s P).
Proof. exact (eq_refl (term431 _102289 _102316 _87593 _87604 A B P s)). Qed.
Lemma lem4074617 {_102289 _102316 _87593 _87604 A B : Type'} (s : _102289 -> Prop) (P : type686 _102316) : term228 _102289 _102316 _87593 _87604 A B s P.
Proof. exact (EQ_MP (@lem4074616 _102289 _102316 _87593 _87604 A B s P) (@lem4074615 _102289 _102316 _87593 _87604 A B P s)). Qed.
Lemma lem4074618 {_102289 _102316 _87593 _87604 A B : Type'} (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : term432 _102289 _102316 _87593 _87604 A B s P f.
Proof. exact (@lem4074617 _102289 _102316 _87593 _87604 A B s P f). Qed.
Lemma lem4074619 {_102289 _102316 _87593 _87604 A B : Type'} (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term432 _102289 _102316 _87593 _87604 A B s P f) = (term224 _102289 _102316 _87593 _87604 A B f s P).
Proof. exact (eq_refl (term432 _102289 _102316 _87593 _87604 A B s P f)). Qed.
Lemma lem4074620 {_102289 _102316 _87593 _87604 A B : Type'} (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : term224 _102289 _102316 _87593 _87604 A B f s P.
Proof. exact (EQ_MP (@lem4074619 _102289 _102316 _87593 _87604 A B f s P) (@lem4074618 _102289 _102316 _87593 _87604 A B s P f)). Qed.
Lemma lem4074621 {_102289 _102316 _87593 _87604 A B : Type'} (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (n : nat) : term433 _102289 _102316 _87593 _87604 A B f s P n.
Proof. exact (@lem4074620 _102289 _102316 _87593 _87604 A B f s P n). Qed.
Lemma lem4074622 {_102289 _102316 _87593 _87604 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : (term433 _102289 _102316 _87593 _87604 A B f s P n) = (term159 _102289 _102316 _87593 _87604 A B n f s P).
Proof. exact (eq_refl (term433 _102289 _102316 _87593 _87604 A B f s P n)). Qed.
Lemma lem4074623 {_102289 _102316 _87593 _87604 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : term159 _102289 _102316 _87593 _87604 A B n f s P.
Proof. exact (EQ_MP (@lem4074622 _102289 _102316 _87593 _87604 A B n f s P) (@lem4074621 _102289 _102316 _87593 _87604 A B f s P n)). Qed.
Lemma lem4074625 {_102289 _102316 _87593 _87604 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : term159 _102289 _102316 _87593 _87604 A B n f s P.
Proof. exact (@lem4069142 _102289 _102316 _87593 _87604 A B n f s P (@lem4074623 _102289 _102316 _87593 _87604 A B n f s P)). Qed.
Lemma lem4074626 {_102289 _102316 _87593 _87604 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term150 _102289 _102316 n f s P) : term218 _102289 _102316 _87593 _87604 A B.
Proof. exact (@lem4074625 _102289 _102316 _87593 _87604 A B n f s P (@lem4069097 _102289 _102316 n f s P h1)). Qed.
Lemma lem4074627 {_102289 _102316 _87593 _87604 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term150 _102289 _102316 n f s P) : term216 _102289 _102316 _87593 _87604 A B.
Proof. exact (@lem4074626 _102289 _102316 _87593 _87604 A B n f s P h1 (@lem4069120 _102289 _102316)). Qed.
Lemma lem4074628 {_102289 _102316 _87593 _87604 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term150 _102289 _102316 n f s P) : term214 _102289 _102316 _87593 _87604 A B.
Proof. exact (@lem4074627 _102289 _102316 _87593 _87604 A B n f s P h1 (@lem4069116 _102289 _87604)). Qed.
Lemma lem4074629 {_102289 _102316 _87593 _87604 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term150 _102289 _102316 n f s P) : term212 _102289 _102316 _87593 _87604 A B.
Proof. exact (@lem4074628 _102289 _102316 _87593 _87604 A B n f s P h1 (@lem4069124 _102289 B)). Qed.
Lemma lem4074630 {_102289 _102316 _87593 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term150 _102289 _102316 n f s P) : term210 _102289 _102316 _87593 A B.
Proof. exact (@lem4074629 _102289 _102316 _87593 Prop A B n f s P h1 (@lem4069117 _102316 Prop)). Qed.
Lemma lem4074631 {_102289 _102316 _87593 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term150 _102289 _102316 n f s P) : term208 _102289 _102316 _87593 A B.
Proof. exact (@lem4074630 _102289 _102316 _87593 A B n f s P h1 (@lem4069123 _102316 B)). Qed.
Lemma lem4074632 {_102289 _102316 _87593 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term150 _102289 _102316 n f s P) : term206 _102289 _102316 _87593 A B.
Proof. exact (@lem4074631 _102289 _102316 _87593 A B n f s P h1 (@lem4069118 _102289 _87593)). Qed.
Lemma lem4074633 {_102289 _102316 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term150 _102289 _102316 n f s P) : term204 _102289 _102316 A B.
Proof. exact (@lem4074632 _102289 _102316 Prop A B n f s P h1 (@lem4069119 _102316 Prop)). Qed.
Lemma lem4074634 {_102289 _102316 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term150 _102289 _102316 n f s P) : term202 _102289 _102316 A B.
Proof. exact (@lem4074633 _102289 _102316 A B n f s P h1 (@lem4069122 _102289 A)). Qed.
Lemma lem4074635 {_102289 _102316 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term150 _102289 _102316 n f s P) : term199 _102289 _102316 A B.
Proof. exact (@lem4074634 _102289 _102316 A B n f s P h1 (@lem4069121 _102316 A)). Qed.
Lemma lem4074636 {_102289 _102316 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term150 _102289 _102316 n f s P) : term196 _102289 _102316 A B.
Proof. exact (@lem4074635 _102289 _102316 A B n f s P h1 (@lem4069126 A B)). Qed.
Lemma lem4074637 {_102289 _102316 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term150 _102289 _102316 n f s P) : term193 _102289 _102316 A B.
Proof. exact (@lem4074636 _102289 _102316 A B n f s P h1 (@lem4069125 B)). Qed.
Lemma lem4074638 {_102289 _102316 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term150 _102289 _102316 n f s P) : term190 _102289 _102316 A B.
Proof. exact (@lem4074637 _102289 _102316 A B n f s P h1 (@lem95173)). Qed.
Lemma lem4074639 {_102289 _102316 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term150 _102289 _102316 n f s P) : term188 _102289 _102316 A B.
Proof. exact (@lem4074638 _102289 _102316 A B n f s P h1 (@lem4069109 _102289 _102316)). Qed.
Lemma lem4074640 {_102289 _102316 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term150 _102289 _102316 n f s P) : term186 _102289 _102316 A B.
Proof. exact (@lem4074639 _102289 _102316 A B n f s P h1 (@lem4069103 _102289 B)). Qed.
Lemma lem4074641 {_102289 _102316 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term150 _102289 _102316 n f s P) : term184 _102289 _102316 A B.
Proof. exact (@lem4074640 _102289 _102316 A B n f s P h1 (@lem4069104 _102316 B)). Qed.
Lemma lem4074642 {_102289 _102316 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term150 _102289 _102316 n f s P) : term182 _102289 _102316 A B.
Proof. exact (@lem4074641 _102289 _102316 A B n f s P h1 (@lem4069107 _102289 A)). Qed.
Lemma lem4074643 {_102289 _102316 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term150 _102289 _102316 n f s P) : term179 _102289 _102316 A B.
Proof. exact (@lem4074642 _102289 _102316 A B n f s P h1 (@lem4069108 _102316 A)). Qed.
Lemma lem4074644 {_102289 _102316 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term150 _102289 _102316 n f s P) : term176 _102289 _102316 A B.
Proof. exact (@lem4074643 _102289 _102316 A B n f s P h1 (@lem4069105 A B)). Qed.
Lemma lem4074645 {_102289 _102316 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term150 _102289 _102316 n f s P) : term173 _102289 _102316 A B.
Proof. exact (@lem4074644 _102289 _102316 A B n f s P h1 (@lem4069106 B)). Qed.
Lemma lem4074646 {_102289 _102316 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term150 _102289 _102316 n f s P) : term171 _102289 _102316 A B.
Proof. exact (@lem4074645 _102289 _102316 A B n f s P h1 (@lem4069102 _102289 _102316)). Qed.
Lemma lem4074647 {_102289 _102316 A B : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term150 _102289 _102316 n f s P) : term169 _102289 _102316 A B.
Proof. exact (@lem4074646 _102289 _102316 A B n f s P h1 (@lem4069098 _102289 B)). Qed.
Lemma lem4074648 {_102289 _102316 A : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term150 _102289 _102316 n f s P) : term166 _102289 _102316 A.
Proof. exact (@lem4074647 _102289 _102316 A Prop n f s P h1 (@lem4069099 _102316 Prop)). Qed.
Lemma lem4074649 {_102289 _102316 A : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term150 _102289 _102316 n f s P) : term163 _102316 A.
Proof. exact (@lem4074648 _102289 _102316 A n f s P h1 (@lem4069100 _102289 A)). Qed.
Lemma lem4074650 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term150 _102289 _102316 n f s P) : False.
Proof. exact (@lem4074649 _102289 _102316 Prop n f s P h1 (@lem4069101 _102316 Prop)). Qed.
Lemma lem4074651 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term150 _102289 _102316 n f s P) : (term150 _102289 _102316 n f s P) = False.
Proof. exact (prop_ext (fun h2 : term150 _102289 _102316 n f s P => @lem4074650 _102289 _102316 n f s P h1) (fun h2 : False => @lem4069097 _102289 _102316 n f s P h1)). Qed.
Lemma lem4074652 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) (h1 : term150 _102289 _102316 n f s P) : False.
Proof. exact (EQ_MP (@lem4074651 _102289 _102316 n f s P h1) (@lem4069097 _102289 _102316 n f s P h1)). Qed.
Lemma lem4074653 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : term149 _102289 _102316 n f s P.
Proof. exact (fun h0 : term150 _102289 _102316 n f s P => @lem4074652 _102289 _102316 n f s P h0). Qed.
Lemma lem4074654 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : term148 _102289 _102316 n f s P.
Proof. exact (EQ_MP (@lem4069096 _102289 _102316 n f s P) (@lem4074653 _102289 _102316 n f s P)). Qed.
Lemma lem4074655 {_102289 _102316 : Type'} (n : nat) (f : _102289 -> _102316) (s : _102289 -> Prop) (P : type686 _102316) : term434 _102289 _102316 n f s P.
Proof. exact (conj (@lem4069092 _102289 _102316 n s P f) (@lem4074654 _102289 _102316 n f s P)). Qed.
Lemma lem4074656 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term434 _102289 _102316 n f s P) = ((term14 _102289 _102316 n f s P) = (term18 _102289 _102316 n s P f)).
Proof. exact (@lem32 (term14 _102289 _102316 n f s P) (term18 _102289 _102316 n s P f)). Qed.
Lemma lem4074657 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term14 _102289 _102316 n f s P) = (term18 _102289 _102316 n s P f).
Proof. exact (EQ_MP (@lem4074656 _102289 _102316 n s P f) (@lem4074655 _102289 _102316 n f s P)). Qed.
Lemma lem4074662 {_102289 _102316 : Type'} (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : term435 _102289 _102316 s P f.
Proof. exact (fun n : nat => @lem4074657 _102289 _102316 n s P f). Qed.
Lemma lem4074667 {_102289 _102316 : Type'} (P : type686 _102316) (f : _102289 -> _102316) : term436 _102289 _102316 P f.
Proof. exact (fun s : _102289 -> Prop => @lem4074662 _102289 _102316 s P f). Qed.
Lemma lem4074672 {_102289 _102316 : Type'} (P : type686 _102316) : term437 _102289 _102316 P.
Proof. exact (fun f : _102289 -> _102316 => @lem4074667 _102289 _102316 P f). Qed.
Lemma lem4074677 {_102289 _102316 : Type'} : term438 _102289 _102316.
Proof. exact (fun P : type686 _102316 => @lem4074672 _102289 _102316 P). Qed.
