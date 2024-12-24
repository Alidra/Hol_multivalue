Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_OPTION_THM_term_abbrevs.
Require Import option_INDUCT_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm32_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem1072129 {A : Type'} (P : type1160 A) : term0 A P.
Proof. exact (@lem1070232 A P). Qed.
Lemma lem1072130 {A : Type'} (P : type1160 A) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem1072131 {A : Type'} (P : type1160 A) : term1 A P.
Proof. exact (EQ_MP (@lem1072130 A P) (@lem1072129 A P)). Qed.
Lemma lem1072132 {A : Type'} (P : type1160 A) : (term1 A P) = ((term1 A P) = True).
Proof. exact (@lem7 (term1 A P)). Qed.
Lemma lem1072149 {A : Type'} (P : type1160 A) : (term1 A P) = True.
Proof. exact (EQ_MP (@lem1072132 A P) (@lem1072131 A P)). Qed.
Lemma lem1072150 {_24424 : Type'} (P : type1160 _24424) : (term1 _24424 P) = True.
Proof. exact (@lem1072149 _24424 P). Qed.
Lemma lem1072151 {_24424 : Type'} (P : type1160 _24424) : True = (term1 _24424 P).
Proof. exact (SYM (@lem1072150 _24424 P)). Qed.
Lemma lem1072152 {_24424 : Type'} (P : type1160 _24424) : term1 _24424 P.
Proof. exact (EQ_MP (@lem1072151 _24424 P) (@lem0)). Qed.
Lemma lem1072156 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term2 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1072157 (p : Prop) (q : Prop) (p' : Prop) : term3 p q p'.
Proof. exact (fun q' : Prop => @lem1072156 p q p' q'). Qed.
Lemma lem1072158 (p : Prop) (q : Prop) : term4 p q.
Proof. exact (fun p' : Prop => @lem1072157 p q p'). Qed.
Lemma lem1072159 {_24424 : Type'} (P : type1160 _24424) : term5 _24424 P.
Proof. exact (@lem1072158 (term6 _24424 P) (term7 _24424 P)). Qed.
Lemma lem1072160 {_24424 : Type'} (P : type1160 _24424) (p' : Prop) : term8 _24424 P p'.
Proof. exact (@lem1072159 _24424 P p'). Qed.
Lemma lem1072161 {_24424 : Type'} (P : type1160 _24424) (p' : Prop) : (term8 _24424 P p') = (term9 _24424 P p').
Proof. exact (eq_refl (term8 _24424 P p')). Qed.
Lemma lem1072162 {_24424 : Type'} (P : type1160 _24424) (p' : Prop) : term9 _24424 P p'.
Proof. exact (EQ_MP (@lem1072161 _24424 P p') (@lem1072160 _24424 P p')). Qed.
Lemma lem1072163 {_24424 : Type'} (P : type1160 _24424) (p' : Prop) (q' : Prop) : term10 _24424 P p' q'.
Proof. exact (@lem1072162 _24424 P p' q'). Qed.
Lemma lem1072164 {_24424 : Type'} (P : type1160 _24424) (p' : Prop) (q' : Prop) : (term10 _24424 P p' q') = (term11 _24424 P p' q').
Proof. exact (eq_refl (term10 _24424 P p' q')). Qed.
Lemma lem1072165 {_24424 : Type'} (P : type1160 _24424) (p' : Prop) (q' : Prop) : term11 _24424 P p' q'.
Proof. exact (EQ_MP (@lem1072164 _24424 P p' q') (@lem1072163 _24424 P p' q')). Qed.
Lemma lem1072170 {_24424 : Type'} (P : type1160 _24424) : (term6 _24424 P) = (term6 _24424 P).
Proof. exact (eq_refl (term6 _24424 P)). Qed.
Lemma lem1072171 {_24424 : Type'} (P : type1160 _24424) (q' : Prop) : term12 _24424 P q'.
Proof. exact (@lem1072165 _24424 P (term6 _24424 P) q'). Qed.
Lemma lem1072172 {_24424 : Type'} (P : type1160 _24424) (q' : Prop) : term13 _24424 P q'.
Proof. exact (@lem1072171 _24424 P q' (@lem1072170 _24424 P)). Qed.
Lemma lem1072173 {_24424 : Type'} (P : type1160 _24424) (h1 : term6 _24424 P) : term6 _24424 P.
Proof. exact (h1). Qed.
Lemma lem1072174 {_24424 : Type'} (x : option _24424) (P : type1160 _24424) (h1 : term6 _24424 P) : term14 _24424 P x.
Proof. exact (@lem1072173 _24424 P h1 x). Qed.
Lemma lem1072175 {_24424 : Type'} (P : type1160 _24424) (x : option _24424) : (term14 _24424 P x) = (P x).
Proof. exact (eq_refl (term14 _24424 P x)). Qed.
Lemma lem1072176 {_24424 : Type'} (x : option _24424) (P : type1160 _24424) (h1 : term6 _24424 P) : P x.
Proof. exact (EQ_MP (@lem1072175 _24424 P x) (@lem1072174 _24424 x P h1)). Qed.
Lemma lem1072177 {_24424 : Type'} (P : type1160 _24424) (x : option _24424) : (P x) = ((P x) = True).
Proof. exact (@lem7 (P x)). Qed.
Lemma lem1072182 {_24424 : Type'} (x : option _24424) (P : type1160 _24424) (h1 : term6 _24424 P) : (P x) = True.
Proof. exact (EQ_MP (@lem1072177 _24424 P x) (@lem1072176 _24424 x P h1)). Qed.
Lemma lem1072183 {_24424 : Type'} (x : option _24424) (P : type1160 _24424) (h1 : term6 _24424 P) : (P x) = True.
Proof. exact (@lem1072182 _24424 x P h1). Qed.
Lemma lem1072184 {_24424 : Type'} (P : type1160 _24424) (h1 : term6 _24424 P) : (P (@None _24424)) = True.
Proof. exact (@lem1072183 _24424 (@None _24424) P h1). Qed.
Lemma lem1072185 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1072186 {_24424 : Type'} (P : type1160 _24424) (h1 : term6 _24424 P) : (term15 _24424 P) = (and True).
Proof. exact (MK_COMB (@lem1072185) (@lem1072184 _24424 P h1)). Qed.
Lemma lem1072192 {_24424 : Type'} (x : option _24424) (P : type1160 _24424) (h1 : term6 _24424 P) : (P x) = True.
Proof. exact (EQ_MP (@lem1072177 _24424 P x) (@lem1072176 _24424 x P h1)). Qed.
Lemma lem1072193 {_24424 : Type'} (x : option _24424) (P : type1160 _24424) (h1 : term6 _24424 P) : (P x) = True.
Proof. exact (@lem1072192 _24424 x P h1). Qed.
Lemma lem1072194 {_24424 : Type'} (a : _24424) (P : type1160 _24424) (h1 : term6 _24424 P) : (term16 _24424 P a) = True.
Proof. exact (@lem1072193 _24424 (@Some _24424 a) P h1). Qed.
Lemma lem1072195 {_24424 : Type'} (P : type1160 _24424) (h1 : term6 _24424 P) : (term17 _24424 P) = (term18 _24424).
Proof. exact (fun_ext (fun a : _24424 => @lem1072194 _24424 a P h1)). Qed.
Lemma lem1072196 {_24424 : Type'} : (@all _24424) = (@all _24424).
Proof. exact (eq_refl (@all _24424)). Qed.
Lemma lem1072197 {_24424 : Type'} (P : type1160 _24424) (h1 : term6 _24424 P) : (term19 _24424 P) = (term20 _24424).
Proof. exact (MK_COMB (@lem1072196 _24424) (@lem1072195 _24424 P h1)). Qed.
Lemma lem1072199 {A : Type'} (t : Prop) : (term21 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1072200 {_24424 : Type'} (t : Prop) : (term21 _24424 t) = t.
Proof. exact (@lem1072199 _24424 t). Qed.
Lemma lem1072201 {_24424 : Type'} : (term20 _24424) = True.
Proof. exact (@lem1072200 _24424 True). Qed.
Lemma lem1072202 {_24424 : Type'} (P : type1160 _24424) (h1 : term6 _24424 P) : (term19 _24424 P) = True.
Proof. exact (TRANS (@lem1072197 _24424 P h1) (@lem1072201 _24424)). Qed.
Lemma lem1072203 {_24424 : Type'} (P : type1160 _24424) (h1 : term6 _24424 P) : (term7 _24424 P) = (True /\ True).
Proof. exact (MK_COMB (@lem1072186 _24424 P h1) (@lem1072202 _24424 P h1)). Qed.
Lemma lem1072205 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1072206 : (True /\ True) = True.
Proof. exact (@lem1072205 True). Qed.
Lemma lem1072207 {_24424 : Type'} (P : type1160 _24424) (h1 : term6 _24424 P) : (term7 _24424 P) = True.
Proof. exact (TRANS (@lem1072203 _24424 P h1) (@lem1072206)). Qed.
Lemma lem1072208 {_24424 : Type'} (P : type1160 _24424) : term22 _24424 P.
Proof. exact (fun h0 : term6 _24424 P => @lem1072207 _24424 P h0). Qed.
Lemma lem1072209 {_24424 : Type'} (P : type1160 _24424) : term23 _24424 P.
Proof. exact (@lem1072172 _24424 P True). Qed.
Lemma lem1072210 {_24424 : Type'} (P : type1160 _24424) : (term24 _24424 P) = (term25 _24424 P).
Proof. exact (@lem1072209 _24424 P (@lem1072208 _24424 P)). Qed.
Lemma lem1072212 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1072213 {_24424 : Type'} (P : type1160 _24424) : (term25 _24424 P) = True.
Proof. exact (@lem1072212 (term6 _24424 P)). Qed.
Lemma lem1072214 {_24424 : Type'} (P : type1160 _24424) : (term24 _24424 P) = True.
Proof. exact (TRANS (@lem1072210 _24424 P) (@lem1072213 _24424 P)). Qed.
Lemma lem1072215 {_24424 : Type'} (P : type1160 _24424) : True = (term24 _24424 P).
Proof. exact (SYM (@lem1072214 _24424 P)). Qed.
Lemma lem1072217 {_24424 : Type'} (P : type1160 _24424) : term24 _24424 P.
Proof. exact (EQ_MP (@lem1072215 _24424 P) (@lem0)). Qed.
Lemma lem1072218 {_24424 : Type'} (P : type1160 _24424) : term26 _24424 P.
Proof. exact (conj (@lem1072217 _24424 P) (@lem1072152 _24424 P)). Qed.
Lemma lem1072219 {_24424 : Type'} (P : type1160 _24424) : (term26 _24424 P) = ((term6 _24424 P) = (term7 _24424 P)).
Proof. exact (@lem32 (term6 _24424 P) (term7 _24424 P)). Qed.
Lemma lem1072220 {_24424 : Type'} (P : type1160 _24424) : (term6 _24424 P) = (term7 _24424 P).
Proof. exact (EQ_MP (@lem1072219 _24424 P) (@lem1072218 _24424 P)). Qed.
Lemma lem1072225 {_24424 : Type'} : term27 _24424.
Proof. exact (fun P : type1160 _24424 => @lem1072220 _24424 P). Qed.
