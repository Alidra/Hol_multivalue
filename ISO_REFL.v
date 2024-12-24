Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ISO_REFL_term_abbrevs.
Require Import ISO_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1845_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1075150 {A B : Type'} (g : B -> A) : term0 A B g.
Proof. exact (@lem1075149 A B g). Qed.
Lemma lem1075151 {A B : Type'} (g : B -> A) : (term0 A B g) = (term1 A B g).
Proof. exact (eq_refl (term0 A B g)). Qed.
Lemma lem1075152 {A B : Type'} (g : B -> A) : term1 A B g.
Proof. exact (EQ_MP (@lem1075151 A B g) (@lem1075150 A B g)). Qed.
Lemma lem1075153 {A B : Type'} (g : B -> A) (f : A -> B) : term2 A B g f.
Proof. exact (@lem1075152 A B g f). Qed.
Lemma lem1075154 {A B : Type'} (g : B -> A) (f : A -> B) : (term2 A B g f) = ((@ExtensionalityFacts.is_inverse A B f g) = (term3 A B g f)).
Proof. exact (eq_refl (term2 A B g f)). Qed.
Lemma lem1075157 {A B : Type'} (g : B -> A) (f : A -> B) : (@ExtensionalityFacts.is_inverse A B f g) = (term3 A B g f).
Proof. exact (EQ_MP (@lem1075154 A B g f) (@lem1075153 A B g f)). Qed.
Lemma lem1075158 {A : Type'} (g : A -> A) (f : A -> A) : (@ExtensionalityFacts.is_inverse A A f g) = (term4 A g f).
Proof. exact (@lem1075157 A A g f). Qed.
Lemma lem1075159 {A : Type'} : (term5 A) = (term6 A).
Proof. exact (@lem1075158 A (term7 A) (term7 A)). Qed.
Lemma lem1075161 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem1845 t)). Qed.
Lemma lem1075162 {A : Type'} : (term6 A) = (term8 A).
Proof. exact (@lem1075161 (term8 A)). Qed.
Lemma lem1075165 {A : Type'} : (term9 A) = (term9 A).
Proof. exact (eq_refl (term9 A)). Qed.
Lemma lem1075166 {A : Type'} : (term9 A) = ((term6 A) = (term8 A)).
Proof. exact (eq_refl (term9 A)). Qed.
Lemma lem1075167 {A : Type'} : (term10 A) = (term10 A).
Proof. exact (eq_refl (term10 A)). Qed.
Lemma lem1075168 {A : Type'} : ((term9 A) = (term9 A)) = ((term9 A) = ((term6 A) = (term8 A))).
Proof. exact (MK_COMB (@lem1075167 A) (@lem1075166 A)). Qed.
Lemma lem1075169 {A : Type'} : (term9 A) = ((term6 A) = (term8 A)).
Proof. exact (eq_refl (term9 A)). Qed.
Lemma lem1075170 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1075171 {A : Type'} : (term10 A) = (term11 A).
Proof. exact (MK_COMB (@lem1075170) (@lem1075169 A)). Qed.
Lemma lem1075172 {A : Type'} : ((term6 A) = (term8 A)) = ((term6 A) = (term8 A)).
Proof. exact (eq_refl ((term6 A) = (term8 A))). Qed.
Lemma lem1075173 {A : Type'} : ((term9 A) = ((term6 A) = (term8 A))) = (((term6 A) = (term8 A)) = ((term6 A) = (term8 A))).
Proof. exact (MK_COMB (@lem1075171 A) (@lem1075172 A)). Qed.
Lemma lem1075174 {A : Type'} : ((term9 A) = (term9 A)) = (((term6 A) = (term8 A)) = ((term6 A) = (term8 A))).
Proof. exact (TRANS (@lem1075168 A) (@lem1075173 A)). Qed.
Lemma lem1075175 {A : Type'} : ((term6 A) = (term8 A)) = ((term6 A) = (term8 A)).
Proof. exact (EQ_MP (@lem1075174 A) (@lem1075165 A)). Qed.
Lemma lem1075176 {A : Type'} : (term6 A) = (term8 A).
Proof. exact (EQ_MP (@lem1075175 A) (@lem1075162 A)). Qed.
Lemma lem1075181 {A : Type'} : (term5 A) = (term8 A).
Proof. exact (TRANS (@lem1075159 A) (@lem1075176 A)). Qed.
Lemma lem1075185 {A B : Type'} (f : A -> B) (y : A) : (term12 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1075186 {A : Type'} (f : A -> A) (y : A) : (term13 A f y) = (f y).
Proof. exact (@lem1075185 A A f y). Qed.
Lemma lem1075187 {A : Type'} (x : A) : (term14 A x) = (term15 A x).
Proof. exact (@lem1075186 A (term7 A) (term16 A x)). Qed.
Lemma lem1075188 {A : Type'} (x : A) : (term16 A x) = x.
Proof. exact (eq_refl (term16 A x)). Qed.
Lemma lem1075189 {A : Type'} : (term17 A) = (term7 A).
Proof. exact (fun_ext (fun x : A => @lem1075188 A x)). Qed.
Lemma lem1075190 {A : Type'} (x : A) : (term16 A x) = (term16 A x).
Proof. exact (eq_refl (term16 A x)). Qed.
Lemma lem1075191 {A : Type'} (x : A) : (term14 A x) = (term15 A x).
Proof. exact (MK_COMB (@lem1075189 A) (@lem1075190 A x)). Qed.
Lemma lem1075192 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1075193 {A : Type'} (x : A) : (term18 A x) = (term19 A x).
Proof. exact (MK_COMB (@lem1075192 A) (@lem1075191 A x)). Qed.
Lemma lem1075194 {A : Type'} (x : A) : (term15 A x) = (term16 A x).
Proof. exact (eq_refl (term15 A x)). Qed.
Lemma lem1075195 {A : Type'} (x : A) : ((term14 A x) = (term15 A x)) = ((term15 A x) = (term16 A x)).
Proof. exact (MK_COMB (@lem1075193 A x) (@lem1075194 A x)). Qed.
Lemma lem1075196 {A : Type'} (x : A) : (term15 A x) = (term16 A x).
Proof. exact (EQ_MP (@lem1075195 A x) (@lem1075187 A x)). Qed.
Lemma lem1075198 {A B : Type'} (f : A -> B) (y : A) : (term12 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1075199 {A : Type'} (f : A -> A) (y : A) : (term13 A f y) = (f y).
Proof. exact (@lem1075198 A A f y). Qed.
Lemma lem1075200 {A : Type'} (x : A) : (term20 A x) = (term16 A x).
Proof. exact (@lem1075199 A (term7 A) x). Qed.
Lemma lem1075201 {A : Type'} (x : A) : (term16 A x) = x.
Proof. exact (eq_refl (term16 A x)). Qed.
Lemma lem1075202 {A : Type'} : (term17 A) = (term7 A).
Proof. exact (fun_ext (fun x : A => @lem1075201 A x)). Qed.
Lemma lem1075203 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1075204 {A : Type'} (x : A) : (term20 A x) = (term16 A x).
Proof. exact (MK_COMB (@lem1075202 A) (@lem1075203 A x)). Qed.
Lemma lem1075205 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1075206 {A : Type'} (x : A) : (term21 A x) = (term22 A x).
Proof. exact (MK_COMB (@lem1075205 A) (@lem1075204 A x)). Qed.
Lemma lem1075207 {A : Type'} (x : A) : (term16 A x) = x.
Proof. exact (eq_refl (term16 A x)). Qed.
Lemma lem1075208 {A : Type'} (x : A) : ((term20 A x) = (term16 A x)) = ((term16 A x) = x).
Proof. exact (MK_COMB (@lem1075206 A x) (@lem1075207 A x)). Qed.
Lemma lem1075209 {A : Type'} (x : A) : (term16 A x) = x.
Proof. exact (EQ_MP (@lem1075208 A x) (@lem1075200 A x)). Qed.
Lemma lem1075210 {A : Type'} (x : A) : (term15 A x) = x.
Proof. exact (TRANS (@lem1075196 A x) (@lem1075209 A x)). Qed.
Lemma lem1075211 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1075212 {A : Type'} (x : A) : (term19 A x) = (@eq A x).
Proof. exact (MK_COMB (@lem1075211 A) (@lem1075210 A x)). Qed.
Lemma lem1075213 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1075214 {A : Type'} (x : A) : ((term15 A x) = x) = (x = x).
Proof. exact (MK_COMB (@lem1075212 A x) (@lem1075213 A x)). Qed.
Lemma lem1075216 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1075217 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1075216 A x). Qed.
Lemma lem1075218 {A : Type'} (x : A) : ((term15 A x) = x) = True.
Proof. exact (TRANS (@lem1075214 A x) (@lem1075217 A x)). Qed.
Lemma lem1075219 {A : Type'} : (term23 A) = (term24 A).
Proof. exact (fun_ext (fun x : A => @lem1075218 A x)). Qed.
Lemma lem1075220 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1075221 {A : Type'} : (term8 A) = (term25 A).
Proof. exact (MK_COMB (@lem1075220 A) (@lem1075219 A)). Qed.
Lemma lem1075223 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1075224 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (@lem1075223 A t). Qed.
Lemma lem1075225 {A : Type'} : (term25 A) = True.
Proof. exact (@lem1075224 A True). Qed.
Lemma lem1075226 {A : Type'} : (term8 A) = True.
Proof. exact (TRANS (@lem1075221 A) (@lem1075225 A)). Qed.
Lemma lem1075227 {A : Type'} : (term5 A) = True.
Proof. exact (TRANS (@lem1075181 A) (@lem1075226 A)). Qed.
Lemma lem1075228 {A : Type'} : True = (term5 A).
Proof. exact (SYM (@lem1075227 A)). Qed.
Lemma lem1075229 {A : Type'} : term5 A.
Proof. exact (EQ_MP (@lem1075228 A) (@lem0)). Qed.
