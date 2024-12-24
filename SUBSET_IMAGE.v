Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUBSET_IMAGE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import IMAGE_SUBSET_spec.
Require Import MONO_EXISTS_spec.
Require Import SUBSET_IMAGE_INJ_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
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
Require Import thm21386_spec.
Require Import thm32_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm69_spec.
Lemma lem3641058 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem3641059 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) : term1 A P Q.
Proof. exact (h1). Qed.
Lemma lem3641060 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) (h2 : term0 A P Q) : term2 A P Q.
Proof. exact (@lem3641058 A P Q h2 (@lem3641059 A P Q h1)). Qed.
Lemma lem3641061 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) : term3 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem3641060 A P Q h1 h0). Qed.
Lemma lem3641062 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem3641063 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) (h2 : term0 A P Q) : term2 A P Q.
Proof. exact (@lem3641061 A P Q h1 (@lem3641062 A P Q h2)). Qed.
Lemma lem3641064 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (fun h0 : term1 A P Q => @lem3641063 A P Q h0 h1). Qed.
Lemma lem3641065 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term4 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem3641064 A P Q h0). Qed.
Lemma lem3641067 {A B : Type'} (f : A -> B) : term5 A B f.
Proof. exact (@lem3641047 A B f). Qed.
Lemma lem3641068 {A B : Type'} (f : A -> B) : (term5 A B f) = (term6 A B f).
Proof. exact (eq_refl (term5 A B f)). Qed.
Lemma lem3641069 {A B : Type'} (f : A -> B) : term6 A B f.
Proof. exact (EQ_MP (@lem3641068 A B f) (@lem3641067 A B f)). Qed.
Lemma lem3641070 {A B : Type'} (f : A -> B) (s : B -> Prop) : term7 A B f s.
Proof. exact (@lem3641069 A B f s). Qed.
Lemma lem3641071 {A B : Type'} (s : B -> Prop) (f : A -> B) : (term7 A B f s) = (term8 A B s f).
Proof. exact (eq_refl (term7 A B f s)). Qed.
Lemma lem3641072 {A B : Type'} (s : B -> Prop) (f : A -> B) : term8 A B s f.
Proof. exact (EQ_MP (@lem3641071 A B s f) (@lem3641070 A B f s)). Qed.
Lemma lem3641073 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : term9 A B s f t.
Proof. exact (@lem3641072 A B s f t). Qed.
Lemma lem3641074 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term9 A B s f t) = ((term10 A B s f t) = (term11 A B t s f)).
Proof. exact (eq_refl (term9 A B s f t)). Qed.
Lemma lem3641087 (p : Prop) : p = (term12 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3641088 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term13 A B s f t) = (term14 A B s f t).
Proof. exact (@lem3641087 (term13 A B s f t)). Qed.
Lemma lem3641089 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term14 A B s f t) = (term13 A B s f t).
Proof. exact (SYM (@lem3641088 A B s f t)). Qed.
Lemma lem3641090 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term15 A B s f t) : term15 A B s f t.
Proof. exact (h1). Qed.
Lemma lem3641091 {_87604 A : Type'} : term16 _87604 A.
Proof. exact (@lem3371475 A _87604). Qed.
Lemma lem3641092 {_87604 B : Type'} : term16 _87604 B.
Proof. exact (@lem3371475 B _87604). Qed.
Lemma lem3641093 {_87593 A : Type'} : term17 _87593 A.
Proof. exact (@lem3371475 _87593 A). Qed.
Lemma lem3641094 {_87593 B : Type'} : term17 _87593 B.
Proof. exact (@lem3371475 _87593 B). Qed.
Lemma lem3641095 {A B : Type'} : term17 A B.
Proof. exact (@lem3371475 A B). Qed.
Lemma lem3641098 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term18 _87593 _87604 A B s f t) : term18 _87593 _87604 A B s f t.
Proof. exact (h1). Qed.
Lemma lem3641099 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : term19 _87593 _87604 A B s f t.
Proof. exact (fun h0 : term18 _87593 _87604 A B s f t => @lem3641098 _87593 _87604 A B s f t h0). Qed.
Lemma lem3641100 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term19 _87593 _87604 A B s f t) : term19 _87593 _87604 A B s f t.
Proof. exact (h1). Qed.
Lemma lem3641101 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term18 _87593 _87604 A B s f t) : term18 _87593 _87604 A B s f t.
Proof. exact (h1). Qed.
Lemma lem3641102 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term18 _87593 _87604 A B s f t) (h2 : term19 _87593 _87604 A B s f t) : term18 _87593 _87604 A B s f t.
Proof. exact (@lem3641100 _87593 _87604 A B s f t h2 (@lem3641101 _87593 _87604 A B s f t h1)). Qed.
Lemma lem3641103 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term18 _87593 _87604 A B s f t) : term20 _87593 _87604 A B s f t.
Proof. exact (fun h0 : term19 _87593 _87604 A B s f t => @lem3641102 _87593 _87604 A B s f t h1 h0). Qed.
Lemma lem3641104 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term19 _87593 _87604 A B s f t) : term19 _87593 _87604 A B s f t.
Proof. exact (h1). Qed.
Lemma lem3641105 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term18 _87593 _87604 A B s f t) (h2 : term19 _87593 _87604 A B s f t) : term18 _87593 _87604 A B s f t.
Proof. exact (@lem3641103 _87593 _87604 A B s f t h1 (@lem3641104 _87593 _87604 A B s f t h2)). Qed.
Lemma lem3641106 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term19 _87593 _87604 A B s f t) : term19 _87593 _87604 A B s f t.
Proof. exact (fun h0 : term18 _87593 _87604 A B s f t => @lem3641105 _87593 _87604 A B s f t h0 h1). Qed.
Lemma lem3641107 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : term21 _87593 _87604 A B s f t.
Proof. exact (fun h0 : term19 _87593 _87604 A B s f t => @lem3641106 _87593 _87604 A B s f t h0). Qed.
Lemma lem3641110 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : term19 _87593 _87604 A B s f t.
Proof. exact (@lem3641107 _87593 _87604 A B s f t (@lem3641099 _87593 _87604 A B s f t)). Qed.
Lemma lem3641111 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : term19 _87593 _87604 A B s f t.
Proof. exact (@lem3641110 _87593 _87604 A B s f t). Qed.
Lemma lem3641243 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3641244 {_87604 B : Type'} : (term22 _87604 B) = (term23 _87604 B).
Proof. exact (@lem3641243 (term16 _87604 B)). Qed.
Lemma lem3641259 {A B : Type'} : (term24 A B) = (term24 A B).
Proof. exact (eq_refl (term24 A B)). Qed.
Lemma lem3641260 {_87604 A B : Type'} : (term25 _87604 A B) = (term26 _87604 A B).
Proof. exact (MK_COMB (@lem3641259 A B) (@lem3641244 _87604 B)). Qed.
Lemma lem3641263 {_87604 A : Type'} : (term27 _87604 A) = (term27 _87604 A).
Proof. exact (eq_refl (term27 _87604 A)). Qed.
Lemma lem3641264 {_87604 A B : Type'} : (term28 _87604 A B) = (term29 _87604 A B).
Proof. exact (MK_COMB (@lem3641263 _87604 A) (@lem3641260 _87604 A B)). Qed.
Lemma lem3641267 {_87593 B : Type'} : (term24 _87593 B) = (term24 _87593 B).
Proof. exact (eq_refl (term24 _87593 B)). Qed.
Lemma lem3641268 {_87593 _87604 A B : Type'} : (term30 _87593 _87604 A B) = (term31 _87593 _87604 A B).
Proof. exact (MK_COMB (@lem3641267 _87593 B) (@lem3641264 _87604 A B)). Qed.
Lemma lem3641271 {_87593 A : Type'} : (term24 _87593 A) = (term24 _87593 A).
Proof. exact (eq_refl (term24 _87593 A)). Qed.
Lemma lem3641272 {_87593 _87604 A B : Type'} : (term32 _87593 _87604 A B) = (term33 _87593 _87604 A B).
Proof. exact (MK_COMB (@lem3641271 _87593 A) (@lem3641268 _87593 _87604 A B)). Qed.
Lemma lem3641275 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term34 A B s f t) = (term34 A B s f t).
Proof. exact (eq_refl (term34 A B s f t)). Qed.
Lemma lem3641276 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term18 _87593 _87604 A B s f t) = (term35 _87593 _87604 A B s f t).
Proof. exact (MK_COMB (@lem3641275 A B s f t) (@lem3641272 _87593 _87604 A B)). Qed.
Lemma lem3641279 {_87593 _87604 A B : Type'} (f : A -> B) (t : A -> Prop) : (term36 _87593 _87604 A B f t) = (term37 _87593 _87604 A B f t).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3641276 _87593 _87604 A B s f t)). Qed.
Lemma lem3641280 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3641281 {_87593 _87604 A B : Type'} (f : A -> B) (t : A -> Prop) : (term38 _87593 _87604 A B f t) = (term39 _87593 _87604 A B f t).
Proof. exact (MK_COMB (@lem3641280 B) (@lem3641279 _87593 _87604 A B f t)). Qed.
Lemma lem3641286 {_87593 _87604 A B : Type'} (t : A -> Prop) : (term40 _87593 _87604 A B t) = (term41 _87593 _87604 A B t).
Proof. exact (fun_ext (fun f : A -> B => @lem3641281 _87593 _87604 A B f t)). Qed.
Lemma lem3641287 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3641288 {_87593 _87604 A B : Type'} (t : A -> Prop) : (term42 _87593 _87604 A B t) = (term43 _87593 _87604 A B t).
Proof. exact (MK_COMB (@lem3641287 A B) (@lem3641286 _87593 _87604 A B t)). Qed.
Lemma lem3641293 {_87593 _87604 A B : Type'} : (term44 _87593 _87604 A B) = (term45 _87593 _87604 A B).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3641288 _87593 _87604 A B t)). Qed.
Lemma lem3641294 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3641303 {_87593 _87604 A B : Type'} : (term46 _87593 _87604 A B) = (term47 _87593 _87604 A B).
Proof. exact (MK_COMB (@lem3641294 A) (@lem3641293 _87593 _87604 A B)). Qed.
Lemma lem3641308 {_87604 B : Type'} (s : B -> Prop) (f : B -> _87604) (t : B -> Prop) : (term48 _87604 B s f t) = (term48 _87604 B s f t).
Proof. exact (eq_refl (term48 _87604 B s f t)). Qed.
Lemma lem3641309 {_87604 B : Type'} (s : B -> Prop) (f : B -> _87604) : (term49 _87604 B s f) = (term49 _87604 B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3641308 _87604 B s f t)). Qed.
Lemma lem3641310 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3641311 {_87604 B : Type'} (s : B -> Prop) (f : B -> _87604) : (term50 _87604 B s f) = (term50 _87604 B s f).
Proof. exact (MK_COMB (@lem3641310 B) (@lem3641309 _87604 B s f)). Qed.
Lemma lem3641312 {_87604 B : Type'} (f : B -> _87604) : (term51 _87604 B f) = (term51 _87604 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3641311 _87604 B s f)). Qed.
Lemma lem3641313 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3641314 {_87604 B : Type'} (f : B -> _87604) : (term52 _87604 B f) = (term52 _87604 B f).
Proof. exact (MK_COMB (@lem3641313 B) (@lem3641312 _87604 B f)). Qed.
Lemma lem3641315 {_87604 B : Type'} : (term53 _87604 B) = (term53 _87604 B).
Proof. exact (fun_ext (fun f : B -> _87604 => @lem3641314 _87604 B f)). Qed.
Lemma lem3641316 {_87604 B : Type'} : (@all (B -> _87604)) = (@all (B -> _87604)).
Proof. exact (eq_refl (@all (B -> _87604))). Qed.
Lemma lem3641317 {_87604 B : Type'} : (term16 _87604 B) = (term16 _87604 B).
Proof. exact (MK_COMB (@lem3641316 _87604 B) (@lem3641315 _87604 B)). Qed.
Lemma lem3641318 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3641319 {_87604 B : Type'} : (term23 _87604 B) = (term23 _87604 B).
Proof. exact (MK_COMB (@lem3641318) (@lem3641317 _87604 B)). Qed.
Lemma lem3641324 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term54 A B s f t) = (term54 A B s f t).
Proof. exact (eq_refl (term54 A B s f t)). Qed.
Lemma lem3641325 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term55 A B s f) = (term55 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3641324 A B s f t)). Qed.
Lemma lem3641326 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3641327 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term56 A B s f) = (term56 A B s f).
Proof. exact (MK_COMB (@lem3641326 A) (@lem3641325 A B s f)). Qed.
Lemma lem3641328 {A B : Type'} (f : A -> B) : (term57 A B f) = (term57 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3641327 A B s f)). Qed.
Lemma lem3641329 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3641330 {A B : Type'} (f : A -> B) : (term58 A B f) = (term58 A B f).
Proof. exact (MK_COMB (@lem3641329 A) (@lem3641328 A B f)). Qed.
Lemma lem3641331 {A B : Type'} : (term59 A B) = (term59 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3641330 A B f)). Qed.
Lemma lem3641332 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3641333 {A B : Type'} : (term17 A B) = (term17 A B).
Proof. exact (MK_COMB (@lem3641332 A B) (@lem3641331 A B)). Qed.
Lemma lem3641334 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3641335 {A B : Type'} : (term24 A B) = (term24 A B).
Proof. exact (MK_COMB (@lem3641334) (@lem3641333 A B)). Qed.
Lemma lem3641336 {_87604 A B : Type'} : (term26 _87604 A B) = (term26 _87604 A B).
Proof. exact (MK_COMB (@lem3641335 A B) (@lem3641319 _87604 B)). Qed.
Lemma lem3641341 {_87604 A : Type'} (s : A -> Prop) (f : A -> _87604) (t : A -> Prop) : (term48 _87604 A s f t) = (term48 _87604 A s f t).
Proof. exact (eq_refl (term48 _87604 A s f t)). Qed.
Lemma lem3641342 {_87604 A : Type'} (s : A -> Prop) (f : A -> _87604) : (term49 _87604 A s f) = (term49 _87604 A s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3641341 _87604 A s f t)). Qed.
Lemma lem3641343 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3641344 {_87604 A : Type'} (s : A -> Prop) (f : A -> _87604) : (term50 _87604 A s f) = (term50 _87604 A s f).
Proof. exact (MK_COMB (@lem3641343 A) (@lem3641342 _87604 A s f)). Qed.
Lemma lem3641345 {_87604 A : Type'} (f : A -> _87604) : (term51 _87604 A f) = (term51 _87604 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3641344 _87604 A s f)). Qed.
Lemma lem3641346 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3641347 {_87604 A : Type'} (f : A -> _87604) : (term52 _87604 A f) = (term52 _87604 A f).
Proof. exact (MK_COMB (@lem3641346 A) (@lem3641345 _87604 A f)). Qed.
Lemma lem3641348 {_87604 A : Type'} : (term53 _87604 A) = (term53 _87604 A).
Proof. exact (fun_ext (fun f : A -> _87604 => @lem3641347 _87604 A f)). Qed.
Lemma lem3641349 {_87604 A : Type'} : (@all (A -> _87604)) = (@all (A -> _87604)).
Proof. exact (eq_refl (@all (A -> _87604))). Qed.
Lemma lem3641350 {_87604 A : Type'} : (term16 _87604 A) = (term16 _87604 A).
Proof. exact (MK_COMB (@lem3641349 _87604 A) (@lem3641348 _87604 A)). Qed.
Lemma lem3641351 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3641352 {_87604 A : Type'} : (term27 _87604 A) = (term27 _87604 A).
Proof. exact (MK_COMB (@lem3641351) (@lem3641350 _87604 A)). Qed.
Lemma lem3641353 {_87604 A B : Type'} : (term29 _87604 A B) = (term29 _87604 A B).
Proof. exact (MK_COMB (@lem3641352 _87604 A) (@lem3641336 _87604 A B)). Qed.
Lemma lem3641358 {_87593 B : Type'} (s : _87593 -> Prop) (f : _87593 -> B) (t : _87593 -> Prop) : (term54 _87593 B s f t) = (term54 _87593 B s f t).
Proof. exact (eq_refl (term54 _87593 B s f t)). Qed.
Lemma lem3641359 {_87593 B : Type'} (s : _87593 -> Prop) (f : _87593 -> B) : (term55 _87593 B s f) = (term55 _87593 B s f).
Proof. exact (fun_ext (fun t : _87593 -> Prop => @lem3641358 _87593 B s f t)). Qed.
Lemma lem3641360 {_87593 : Type'} : (@all (_87593 -> Prop)) = (@all (_87593 -> Prop)).
Proof. exact (eq_refl (@all (_87593 -> Prop))). Qed.
Lemma lem3641361 {_87593 B : Type'} (s : _87593 -> Prop) (f : _87593 -> B) : (term56 _87593 B s f) = (term56 _87593 B s f).
Proof. exact (MK_COMB (@lem3641360 _87593) (@lem3641359 _87593 B s f)). Qed.
Lemma lem3641362 {_87593 B : Type'} (f : _87593 -> B) : (term57 _87593 B f) = (term57 _87593 B f).
Proof. exact (fun_ext (fun s : _87593 -> Prop => @lem3641361 _87593 B s f)). Qed.
Lemma lem3641363 {_87593 : Type'} : (@all (_87593 -> Prop)) = (@all (_87593 -> Prop)).
Proof. exact (eq_refl (@all (_87593 -> Prop))). Qed.
Lemma lem3641364 {_87593 B : Type'} (f : _87593 -> B) : (term58 _87593 B f) = (term58 _87593 B f).
Proof. exact (MK_COMB (@lem3641363 _87593) (@lem3641362 _87593 B f)). Qed.
Lemma lem3641365 {_87593 B : Type'} : (term59 _87593 B) = (term59 _87593 B).
Proof. exact (fun_ext (fun f : _87593 -> B => @lem3641364 _87593 B f)). Qed.
Lemma lem3641366 {_87593 B : Type'} : (@all (_87593 -> B)) = (@all (_87593 -> B)).
Proof. exact (eq_refl (@all (_87593 -> B))). Qed.
Lemma lem3641367 {_87593 B : Type'} : (term17 _87593 B) = (term17 _87593 B).
Proof. exact (MK_COMB (@lem3641366 _87593 B) (@lem3641365 _87593 B)). Qed.
Lemma lem3641368 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3641369 {_87593 B : Type'} : (term24 _87593 B) = (term24 _87593 B).
Proof. exact (MK_COMB (@lem3641368) (@lem3641367 _87593 B)). Qed.
Lemma lem3641370 {_87593 _87604 A B : Type'} : (term31 _87593 _87604 A B) = (term31 _87593 _87604 A B).
Proof. exact (MK_COMB (@lem3641369 _87593 B) (@lem3641353 _87604 A B)). Qed.
Lemma lem3641375 {_87593 A : Type'} (s : _87593 -> Prop) (f : _87593 -> A) (t : _87593 -> Prop) : (term54 _87593 A s f t) = (term54 _87593 A s f t).
Proof. exact (eq_refl (term54 _87593 A s f t)). Qed.
Lemma lem3641376 {_87593 A : Type'} (s : _87593 -> Prop) (f : _87593 -> A) : (term55 _87593 A s f) = (term55 _87593 A s f).
Proof. exact (fun_ext (fun t : _87593 -> Prop => @lem3641375 _87593 A s f t)). Qed.
Lemma lem3641377 {_87593 : Type'} : (@all (_87593 -> Prop)) = (@all (_87593 -> Prop)).
Proof. exact (eq_refl (@all (_87593 -> Prop))). Qed.
Lemma lem3641378 {_87593 A : Type'} (s : _87593 -> Prop) (f : _87593 -> A) : (term56 _87593 A s f) = (term56 _87593 A s f).
Proof. exact (MK_COMB (@lem3641377 _87593) (@lem3641376 _87593 A s f)). Qed.
Lemma lem3641379 {_87593 A : Type'} (f : _87593 -> A) : (term57 _87593 A f) = (term57 _87593 A f).
Proof. exact (fun_ext (fun s : _87593 -> Prop => @lem3641378 _87593 A s f)). Qed.
Lemma lem3641380 {_87593 : Type'} : (@all (_87593 -> Prop)) = (@all (_87593 -> Prop)).
Proof. exact (eq_refl (@all (_87593 -> Prop))). Qed.
Lemma lem3641381 {_87593 A : Type'} (f : _87593 -> A) : (term58 _87593 A f) = (term58 _87593 A f).
Proof. exact (MK_COMB (@lem3641380 _87593) (@lem3641379 _87593 A f)). Qed.
Lemma lem3641382 {_87593 A : Type'} : (term59 _87593 A) = (term59 _87593 A).
Proof. exact (fun_ext (fun f : _87593 -> A => @lem3641381 _87593 A f)). Qed.
Lemma lem3641383 {_87593 A : Type'} : (@all (_87593 -> A)) = (@all (_87593 -> A)).
Proof. exact (eq_refl (@all (_87593 -> A))). Qed.
Lemma lem3641384 {_87593 A : Type'} : (term17 _87593 A) = (term17 _87593 A).
Proof. exact (MK_COMB (@lem3641383 _87593 A) (@lem3641382 _87593 A)). Qed.
Lemma lem3641385 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3641386 {_87593 A : Type'} : (term24 _87593 A) = (term24 _87593 A).
Proof. exact (MK_COMB (@lem3641385) (@lem3641384 _87593 A)). Qed.
Lemma lem3641387 {_87593 _87604 A B : Type'} : (term33 _87593 _87604 A B) = (term33 _87593 _87604 A B).
Proof. exact (MK_COMB (@lem3641386 _87593 A) (@lem3641370 _87593 _87604 A B)). Qed.
Lemma lem3641388 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term10 A B s f t) = (term10 A B s f t).
Proof. exact (eq_refl (term10 A B s f t)). Qed.
Lemma lem3641393 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term60 A B t s f u) = (term60 A B t s f u).
Proof. exact (eq_refl (term60 A B t s f u)). Qed.
Lemma lem3641394 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term61 A B t s f) = (term61 A B t s f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3641393 A B t s f u)). Qed.
Lemma lem3641395 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3641396 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term62 A B t s f) = (term62 A B t s f).
Proof. exact (MK_COMB (@lem3641395 A) (@lem3641394 A B t s f)). Qed.
Lemma lem3641397 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3641398 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term63 A B t s f) = (term63 A B t s f).
Proof. exact (MK_COMB (@lem3641397) (@lem3641396 A B t s f)). Qed.
Lemma lem3641399 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term13 A B s f t) = (term13 A B s f t).
Proof. exact (MK_COMB (@lem3641398 A B t s f) (@lem3641388 A B s f t)). Qed.
Lemma lem3641400 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3641401 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term15 A B s f t) = (term15 A B s f t).
Proof. exact (MK_COMB (@lem3641400) (@lem3641399 A B s f t)). Qed.
Lemma lem3641402 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3641403 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term34 A B s f t) = (term34 A B s f t).
Proof. exact (MK_COMB (@lem3641402) (@lem3641401 A B s f t)). Qed.
Lemma lem3641404 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term35 _87593 _87604 A B s f t) = (term35 _87593 _87604 A B s f t).
Proof. exact (MK_COMB (@lem3641403 A B s f t) (@lem3641387 _87593 _87604 A B)). Qed.
Lemma lem3641405 {_87593 _87604 A B : Type'} (f : A -> B) (t : A -> Prop) : (term37 _87593 _87604 A B f t) = (term37 _87593 _87604 A B f t).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3641404 _87593 _87604 A B s f t)). Qed.
Lemma lem3641406 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3641407 {_87593 _87604 A B : Type'} (f : A -> B) (t : A -> Prop) : (term39 _87593 _87604 A B f t) = (term39 _87593 _87604 A B f t).
Proof. exact (MK_COMB (@lem3641406 B) (@lem3641405 _87593 _87604 A B f t)). Qed.
Lemma lem3641408 {_87593 _87604 A B : Type'} (t : A -> Prop) : (term41 _87593 _87604 A B t) = (term41 _87593 _87604 A B t).
Proof. exact (fun_ext (fun f : A -> B => @lem3641407 _87593 _87604 A B f t)). Qed.
Lemma lem3641409 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3641410 {_87593 _87604 A B : Type'} (t : A -> Prop) : (term43 _87593 _87604 A B t) = (term43 _87593 _87604 A B t).
Proof. exact (MK_COMB (@lem3641409 A B) (@lem3641408 _87593 _87604 A B t)). Qed.
Lemma lem3641411 {_87593 _87604 A B : Type'} : (term45 _87593 _87604 A B) = (term45 _87593 _87604 A B).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3641410 _87593 _87604 A B t)). Qed.
Lemma lem3641412 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3641413 {_87593 _87604 A B : Type'} : (term47 _87593 _87604 A B) = (term47 _87593 _87604 A B).
Proof. exact (MK_COMB (@lem3641412 A) (@lem3641411 _87593 _87604 A B)). Qed.
Lemma lem3641554 {_87593 _87604 A B : Type'} : (term46 _87593 _87604 A B) = (term47 _87593 _87604 A B).
Proof. exact (TRANS (@lem3641303 _87593 _87604 A B) (@lem3641413 _87593 _87604 A B)). Qed.
Lemma lem3641555 {_87593 _87604 A B : Type'} : (term47 _87593 _87604 A B) = (term46 _87593 _87604 A B).
Proof. exact (SYM (@lem3641554 _87593 _87604 A B)). Qed.
Lemma lem3641556 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term15 A B s f t) : term15 A B s f t.
Proof. exact (h1). Qed.
Lemma lem3641560 {A B : Type'} (h1 : term17 A B) : term17 A B.
Proof. exact (h1). Qed.
Lemma lem3641566 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term60 A B t s f u) = (term60 A B t s f u).
Proof. exact (eq_refl (term60 A B t s f u)). Qed.
Lemma lem3641567 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term61 A B t s f) = (term61 A B t s f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3641566 A B t s f u)). Qed.
Lemma lem3641568 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3641569 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term62 A B t s f) = (term62 A B t s f).
Proof. exact (MK_COMB (@lem3641568 A) (@lem3641567 A B t s f)). Qed.
Lemma lem3641570 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term64 A B s f t) = (term64 A B s f t).
Proof. exact (eq_refl (term64 A B s f t)). Qed.
Lemma lem3641571 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3641572 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term65 A B t s f) = (term65 A B t s f).
Proof. exact (MK_COMB (@lem3641571) (@lem3641569 A B t s f)). Qed.
Lemma lem3641573 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term66 A B s f t) = (term66 A B s f t).
Proof. exact (MK_COMB (@lem3641572 A B t s f) (@lem3641570 A B s f t)). Qed.
Lemma lem3641574 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term15 A B s f t) = (term66 A B s f t).
Proof. exact (@lem17362 (term62 A B t s f) (term10 A B s f t)). Qed.
Lemma lem3641575 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term15 A B s f t) = (term66 A B s f t).
Proof. exact (TRANS (@lem3641574 A B s f t) (@lem3641573 A B s f t)). Qed.
Lemma lem3641626 {A : Type'} (P : A -> Prop) (Q : Prop) : (term67 A P Q) = (term68 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3641627 {A : Type'} (P : type686 A) (Q : Prop) : (term69 A P Q) = (term70 A P Q).
Proof. exact (@lem3641626 (A -> Prop) P Q). Qed.
Lemma lem3641628 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term71 A B s f t) = (term72 A B s f t).
Proof. exact (@lem3641627 A (term61 A B t s f) (term64 A B s f t)). Qed.
Lemma lem3641629 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term73 A B t s f u) = (term60 A B t s f u).
Proof. exact (eq_refl (term73 A B t s f u)). Qed.
Lemma lem3641630 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term74 A B t s f) = (term61 A B t s f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3641629 A B t s f u)). Qed.
Lemma lem3641631 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3641632 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term75 A B t s f) = (term62 A B t s f).
Proof. exact (MK_COMB (@lem3641631 A) (@lem3641630 A B t s f)). Qed.
Lemma lem3641633 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3641634 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term76 A B t s f) = (term65 A B t s f).
Proof. exact (MK_COMB (@lem3641633) (@lem3641632 A B t s f)). Qed.
Lemma lem3641635 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term64 A B s f t) = (term64 A B s f t).
Proof. exact (eq_refl (term64 A B s f t)). Qed.
Lemma lem3641636 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term71 A B s f t) = (term66 A B s f t).
Proof. exact (MK_COMB (@lem3641634 A B t s f) (@lem3641635 A B s f t)). Qed.
Lemma lem3641637 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3641638 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term77 A B s f t) = (term78 A B s f t).
Proof. exact (MK_COMB (@lem3641637) (@lem3641636 A B s f t)). Qed.
Lemma lem3641639 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term73 A B t s f u) = (term60 A B t s f u).
Proof. exact (eq_refl (term73 A B t s f u)). Qed.
Lemma lem3641640 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3641641 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term79 A B t s f u) = (term80 A B t s f u).
Proof. exact (MK_COMB (@lem3641640) (@lem3641639 A B t s f u)). Qed.
Lemma lem3641642 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term64 A B s f t) = (term64 A B s f t).
Proof. exact (eq_refl (term64 A B s f t)). Qed.
Lemma lem3641643 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term81 A B u s f t) = (term82 A B u s f t).
Proof. exact (MK_COMB (@lem3641641 A B t s f u) (@lem3641642 A B s f t)). Qed.
Lemma lem3641644 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term83 A B s f t) = (term84 A B s f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3641643 A B u s f t)). Qed.
Lemma lem3641645 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3641646 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term72 A B s f t) = (term85 A B s f t).
Proof. exact (MK_COMB (@lem3641645 A) (@lem3641644 A B s f t)). Qed.
Lemma lem3641647 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : ((term71 A B s f t) = (term72 A B s f t)) = ((term66 A B s f t) = (term85 A B s f t)).
Proof. exact (MK_COMB (@lem3641638 A B s f t) (@lem3641646 A B s f t)). Qed.
Lemma lem3641649 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term66 A B s f t) = (term85 A B s f t).
Proof. exact (EQ_MP (@lem3641647 A B s f t) (@lem3641628 A B s f t)). Qed.
Lemma lem3641650 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term15 A B s f t) = (term85 A B s f t).
Proof. exact (TRANS (@lem3641575 A B s f t) (@lem3641649 A B s f t)). Qed.
Lemma lem3641651 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term15 A B s f t) : term85 A B s f t.
Proof. exact (EQ_MP (@lem3641650 A B s f t) (@lem3641556 A B s f t h1)). Qed.
Lemma lem3641889 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term54 A B s f t) = (term86 A B s f t).
Proof. exact (@lem17265 (@SUBSET A s t) (term87 A B s f t)). Qed.
Lemma lem3641890 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term55 A B s f) = (term88 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3641889 A B s f t)). Qed.
Lemma lem3641891 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3641892 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term56 A B s f) = (term89 A B s f).
Proof. exact (MK_COMB (@lem3641891 A) (@lem3641890 A B s f)). Qed.
Lemma lem3641893 {A B : Type'} (f : A -> B) : (term57 A B f) = (term90 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3641892 A B s f)). Qed.
Lemma lem3641894 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3641895 {A B : Type'} (f : A -> B) : (term58 A B f) = (term91 A B f).
Proof. exact (MK_COMB (@lem3641894 A) (@lem3641893 A B f)). Qed.
Lemma lem3641896 {A B : Type'} : (term59 A B) = (term92 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3641895 A B f)). Qed.
Lemma lem3641897 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3641958 {A B : Type'} : (term17 A B) = (term93 A B).
Proof. exact (MK_COMB (@lem3641897 A B) (@lem3641896 A B)). Qed.
Lemma lem3641959 {A B : Type'} (h1 : term17 A B) : term93 A B.
Proof. exact (EQ_MP (@lem3641958 A B) (@lem3641560 A B h1)). Qed.
Lemma lem3642159 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term86 A B s f t) = (term86 A B s f t).
Proof. exact (eq_refl (term86 A B s f t)). Qed.
Lemma lem3642160 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term88 A B s f) = (term88 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3642159 A B s f t)). Qed.
Lemma lem3642161 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3642162 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term89 A B s f) = (term89 A B s f).
Proof. exact (MK_COMB (@lem3642161 A) (@lem3642160 A B s f)). Qed.
Lemma lem3642163 {A B : Type'} (f : A -> B) : (term90 A B f) = (term90 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3642162 A B s f)). Qed.
Lemma lem3642164 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3642165 {A B : Type'} (f : A -> B) : (term91 A B f) = (term91 A B f).
Proof. exact (MK_COMB (@lem3642164 A) (@lem3642163 A B f)). Qed.
Lemma lem3642166 {A B : Type'} : (term92 A B) = (term92 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3642165 A B f)). Qed.
Lemma lem3642167 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3642168 {A B : Type'} : (term93 A B) = (term93 A B).
Proof. exact (MK_COMB (@lem3642167 A B) (@lem3642166 A B)). Qed.
Lemma lem3642169 {A B : Type'} (h1 : term17 A B) : term93 A B.
Proof. exact (EQ_MP (@lem3642168 A B) (@lem3641959 A B h1)). Qed.
Lemma lem3642234 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term82 A B u s f t) : term82 A B u s f t.
Proof. exact (h1). Qed.
Lemma lem3642236 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term82 A B u s f t) : term60 A B t s f u.
Proof. exact (proj1 (@lem3642234 A B u s f t h1)). Qed.
Lemma lem3642303 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term86 A B s f t) = (term86 A B s f t).
Proof. exact (eq_refl (term86 A B s f t)). Qed.
Lemma lem3642304 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term88 A B s f) = (term88 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3642303 A B s f t)). Qed.
Lemma lem3642305 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3642306 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term89 A B s f) = (term89 A B s f).
Proof. exact (MK_COMB (@lem3642305 A) (@lem3642304 A B s f)). Qed.
Lemma lem3642307 {A B : Type'} (f : A -> B) : (term90 A B f) = (term90 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3642306 A B s f)). Qed.
Lemma lem3642308 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3642309 {A B : Type'} (f : A -> B) : (term91 A B f) = (term91 A B f).
Proof. exact (MK_COMB (@lem3642308 A) (@lem3642307 A B f)). Qed.
Lemma lem3642310 {A B : Type'} : (term92 A B) = (term92 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3642309 A B f)). Qed.
Lemma lem3642311 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3642313 {A B : Type'} : (term93 A B) = (term93 A B).
Proof. exact (MK_COMB (@lem3642311 A B) (@lem3642310 A B)). Qed.
Lemma lem3642314 {A B : Type'} (h1 : term17 A B) : term93 A B.
Proof. exact (EQ_MP (@lem3642313 A B) (@lem3642169 A B h1)). Qed.
Lemma lem3642373 {A B : Type'} (_39916 : A -> B) (h1 : term17 A B) : term94 A B _39916.
Proof. exact (@lem3642314 A B h1 _39916). Qed.
Lemma lem3642374 {A B : Type'} (_39916 : A -> B) : (term94 A B _39916) = (term91 A B _39916).
Proof. exact (eq_refl (term94 A B _39916)). Qed.
Lemma lem3642375 {A B : Type'} (_39916 : A -> B) (h1 : term17 A B) : term91 A B _39916.
Proof. exact (EQ_MP (@lem3642374 A B _39916) (@lem3642373 A B _39916 h1)). Qed.
Lemma lem3642376 {A B : Type'} (_39916 : A -> B) (_39917 : A -> Prop) (h1 : term17 A B) : term95 A B _39916 _39917.
Proof. exact (@lem3642375 A B _39916 h1 _39917). Qed.
Lemma lem3642377 {A B : Type'} (_39917 : A -> Prop) (_39916 : A -> B) : (term95 A B _39916 _39917) = (term89 A B _39917 _39916).
Proof. exact (eq_refl (term95 A B _39916 _39917)). Qed.
Lemma lem3642378 {A B : Type'} (_39917 : A -> Prop) (_39916 : A -> B) (h1 : term17 A B) : term89 A B _39917 _39916.
Proof. exact (EQ_MP (@lem3642377 A B _39917 _39916) (@lem3642376 A B _39916 _39917 h1)). Qed.
Lemma lem3642379 {A B : Type'} (_39917 : A -> Prop) (_39916 : A -> B) (_39918 : A -> Prop) (h1 : term17 A B) : term96 A B _39917 _39916 _39918.
Proof. exact (@lem3642378 A B _39917 _39916 h1 _39918). Qed.
Lemma lem3642380 {A B : Type'} (_39917 : A -> Prop) (_39916 : A -> B) (_39918 : A -> Prop) : (term96 A B _39917 _39916 _39918) = (term86 A B _39917 _39916 _39918).
Proof. exact (eq_refl (term96 A B _39917 _39916 _39918)). Qed.
Lemma lem3642422 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term82 A B u s f t) : term64 A B s f t.
Proof. exact (proj2 (@lem3642234 A B u s f t h1)). Qed.
Lemma lem3642426 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term82 A B u s f t) : s = (@IMAGE A B f u).
Proof. exact (proj2 (@lem3642236 A B u s f t h1)). Qed.
Lemma lem3642496 {A B : Type'} (_39917 : A -> Prop) (_39916 : A -> B) (_39918 : A -> Prop) (h1 : term17 A B) : term86 A B _39917 _39916 _39918.
Proof. exact (EQ_MP (@lem3642380 A B _39917 _39916 _39918) (@lem3642379 A B _39917 _39916 _39918 h1)). Qed.
Lemma lem3642511 {A B : Type'} (f : A -> B) (t : A -> Prop) : (term97 A B f t) = (term97 A B f t).
Proof. exact (eq_refl (term97 A B f t)). Qed.
Lemma lem3642512 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term82 A B u s f t) : (term98 A B f t s) = (term99 A B t f u).
Proof. exact (MK_COMB (@lem3642511 A B f t) (@lem3642426 A B u s f t h1)). Qed.
Lemma lem3642513 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term99 A B t f u) = (term100 A B u f t).
Proof. exact (eq_refl (term99 A B t f u)). Qed.
Lemma lem3642514 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : B -> Prop) : (term101 A B f t s) = (term101 A B f t s).
Proof. exact (eq_refl (term101 A B f t s)). Qed.
Lemma lem3642515 {A B : Type'} (s : B -> Prop) (u : A -> Prop) (f : A -> B) (t : A -> Prop) : ((term98 A B f t s) = (term99 A B t f u)) = ((term98 A B f t s) = (term100 A B u f t)).
Proof. exact (MK_COMB (@lem3642514 A B f t s) (@lem3642513 A B u f t)). Qed.
Lemma lem3642516 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term98 A B f t s) = (term64 A B s f t).
Proof. exact (eq_refl (term98 A B f t s)). Qed.
Lemma lem3642517 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3642518 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term101 A B f t s) = (term102 A B s f t).
Proof. exact (MK_COMB (@lem3642517) (@lem3642516 A B s f t)). Qed.
Lemma lem3642519 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term100 A B u f t) = (term100 A B u f t).
Proof. exact (eq_refl (term100 A B u f t)). Qed.
Lemma lem3642520 {A B : Type'} (s : B -> Prop) (u : A -> Prop) (f : A -> B) (t : A -> Prop) : ((term98 A B f t s) = (term100 A B u f t)) = ((term64 A B s f t) = (term100 A B u f t)).
Proof. exact (MK_COMB (@lem3642518 A B s f t) (@lem3642519 A B u f t)). Qed.
Lemma lem3642521 {A B : Type'} (s : B -> Prop) (u : A -> Prop) (f : A -> B) (t : A -> Prop) : ((term98 A B f t s) = (term99 A B t f u)) = ((term64 A B s f t) = (term100 A B u f t)).
Proof. exact (TRANS (@lem3642515 A B s u f t) (@lem3642520 A B s u f t)). Qed.
Lemma lem3642522 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term82 A B u s f t) : (term64 A B s f t) = (term100 A B u f t).
Proof. exact (EQ_MP (@lem3642521 A B s u f t) (@lem3642512 A B u s f t h1)). Qed.
Lemma lem3642523 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term82 A B u s f t) : term100 A B u f t.
Proof. exact (EQ_MP (@lem3642522 A B u s f t h1) (@lem3642422 A B u s f t h1)). Qed.
Lemma lem3642539 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term82 A B u s f t) : @SUBSET A u t.
Proof. exact (proj1 (@lem3642236 A B u s f t h1)). Qed.
Lemma lem3642540 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term82 A B u s f t) : term103 A u t.
Proof. exact (fun h0 : term104 A u t => @lem3642539 A B u s f t h1). Qed.
Lemma lem3642542 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3642543 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term103 A u t) = (@SUBSET A u t).
Proof. exact (@lem3642542 (@SUBSET A u t)). Qed.
Lemma lem3642544 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term82 A B u s f t) : @SUBSET A u t.
Proof. exact (EQ_MP (@lem3642543 A u t) (@lem3642540 A B u s f t h1)). Qed.
Lemma lem3642550 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3642551 {A B : Type'} (_39916 : A -> B) (_39917 : A -> Prop) (_39918 : A -> Prop) : (term86 A B _39917 _39916 _39918) = (term106 A B _39916 _39917 _39918).
Proof. exact (@lem3642550 (term87 A B _39917 _39916 _39918) (term104 A _39917 _39918)). Qed.
Lemma lem3642557 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3642558 {A B : Type'} (_39916 : A -> B) (_39917 : A -> Prop) (_39918 : A -> Prop) : (term107 A B _39917 _39916 _39918) = (term108 A B _39916 _39917 _39918).
Proof. exact (MK_COMB (@lem3642557) (@lem3642551 A B _39916 _39917 _39918)). Qed.
Lemma lem3642564 {A B : Type'} (_39916 : A -> B) (_39917 : A -> Prop) (_39918 : A -> Prop) : (term106 A B _39916 _39917 _39918) = (term106 A B _39916 _39917 _39918).
Proof. exact (eq_refl (term106 A B _39916 _39917 _39918)). Qed.
Lemma lem3642565 {A B : Type'} (_39916 : A -> B) (_39917 : A -> Prop) (_39918 : A -> Prop) : ((term86 A B _39917 _39916 _39918) = (term106 A B _39916 _39917 _39918)) = ((term106 A B _39916 _39917 _39918) = (term106 A B _39916 _39917 _39918)).
Proof. exact (MK_COMB (@lem3642558 A B _39916 _39917 _39918) (@lem3642564 A B _39916 _39917 _39918)). Qed.
Lemma lem3642567 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3642568 (x : Prop) : (x = x) = True.
Proof. exact (@lem3642567 Prop x). Qed.
Lemma lem3642569 {A B : Type'} (_39916 : A -> B) (_39917 : A -> Prop) (_39918 : A -> Prop) : ((term106 A B _39916 _39917 _39918) = (term106 A B _39916 _39917 _39918)) = True.
Proof. exact (@lem3642568 (term106 A B _39916 _39917 _39918)). Qed.
Lemma lem3642570 {A B : Type'} (_39916 : A -> B) (_39917 : A -> Prop) (_39918 : A -> Prop) : ((term86 A B _39917 _39916 _39918) = (term106 A B _39916 _39917 _39918)) = True.
Proof. exact (TRANS (@lem3642565 A B _39916 _39917 _39918) (@lem3642569 A B _39916 _39917 _39918)). Qed.
Lemma lem3642571 {A B : Type'} (_39916 : A -> B) (_39917 : A -> Prop) (_39918 : A -> Prop) : True = ((term86 A B _39917 _39916 _39918) = (term106 A B _39916 _39917 _39918)).
Proof. exact (SYM (@lem3642570 A B _39916 _39917 _39918)). Qed.
Lemma lem3642572 {A B : Type'} (_39916 : A -> B) (_39917 : A -> Prop) (_39918 : A -> Prop) : (term86 A B _39917 _39916 _39918) = (term106 A B _39916 _39917 _39918).
Proof. exact (EQ_MP (@lem3642571 A B _39916 _39917 _39918) (@lem0)). Qed.
Lemma lem3642573 {A B : Type'} (_39916 : A -> B) (_39917 : A -> Prop) (_39918 : A -> Prop) (h1 : term17 A B) : term106 A B _39916 _39917 _39918.
Proof. exact (EQ_MP (@lem3642572 A B _39916 _39917 _39918) (@lem3642496 A B _39917 _39916 _39918 h1)). Qed.
Lemma lem3642575 (b : Prop) (a : Prop) : (a \/ b) = (term109 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3642576 {A B : Type'} (_39917 : A -> Prop) (_39916 : A -> B) (_39918 : A -> Prop) : (term106 A B _39916 _39917 _39918) = (term110 A B _39917 _39916 _39918).
Proof. exact (@lem3642575 (term104 A _39917 _39918) (term87 A B _39917 _39916 _39918)). Qed.
Lemma lem3642578 (a : Prop) : (term111 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3642579 {A : Type'} (_39917 : A -> Prop) (_39918 : A -> Prop) : (term112 A _39917 _39918) = (@SUBSET A _39917 _39918).
Proof. exact (@lem3642578 (@SUBSET A _39917 _39918)). Qed.
Lemma lem3642580 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3642581 {A : Type'} (_39917 : A -> Prop) (_39918 : A -> Prop) : (term113 A _39917 _39918) = (term114 A _39917 _39918).
Proof. exact (MK_COMB (@lem3642580) (@lem3642579 A _39917 _39918)). Qed.
Lemma lem3642582 {A B : Type'} (_39917 : A -> Prop) (_39916 : A -> B) (_39918 : A -> Prop) : (term87 A B _39917 _39916 _39918) = (term87 A B _39917 _39916 _39918).
Proof. exact (eq_refl (term87 A B _39917 _39916 _39918)). Qed.
Lemma lem3642583 {A B : Type'} (_39917 : A -> Prop) (_39916 : A -> B) (_39918 : A -> Prop) : (term110 A B _39917 _39916 _39918) = (term54 A B _39917 _39916 _39918).
Proof. exact (MK_COMB (@lem3642581 A _39917 _39918) (@lem3642582 A B _39917 _39916 _39918)). Qed.
Lemma lem3642584 {A B : Type'} (_39917 : A -> Prop) (_39916 : A -> B) (_39918 : A -> Prop) : (term106 A B _39916 _39917 _39918) = (term54 A B _39917 _39916 _39918).
Proof. exact (TRANS (@lem3642576 A B _39917 _39916 _39918) (@lem3642583 A B _39917 _39916 _39918)). Qed.
Lemma lem3642587 {A B : Type'} (_39917 : A -> Prop) (_39916 : A -> B) (_39918 : A -> Prop) (h1 : term17 A B) : term54 A B _39917 _39916 _39918.
Proof. exact (EQ_MP (@lem3642584 A B _39917 _39916 _39918) (@lem3642573 A B _39916 _39917 _39918 h1)). Qed.
Lemma lem3642588 {A B : Type'} (_39917 : A -> Prop) (_39916 : A -> B) (_39918 : A -> Prop) (h1 : term17 A B) : term54 A B _39917 _39916 _39918.
Proof. exact (@lem3642587 A B _39917 _39916 _39918 h1). Qed.
Lemma lem3642589 {A B : Type'} (u : A -> Prop) (_39916 : A -> B) (t : A -> Prop) (h1 : term17 A B) : term54 A B u _39916 t.
Proof. exact (@lem3642588 A B u _39916 t h1). Qed.
Lemma lem3642592 {A B : Type'} (_39916 : A -> B) (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term17 A B) (h2 : term82 A B u s f t) : term87 A B u _39916 t.
Proof. exact (@lem3642589 A B u _39916 t h1 (@lem3642544 A B u s f t h2)). Qed.
Lemma lem3642593 {A B : Type'} (_39916 : A -> B) (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term17 A B) (h2 : term82 A B u s f t) : term87 A B u _39916 t.
Proof. exact (@lem3642592 A B _39916 u s f t h1 h2). Qed.
Lemma lem3642594 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term17 A B) (h2 : term82 A B u s f t) : term87 A B u f t.
Proof. exact (@lem3642593 A B f u s f t h1 h2). Qed.
Lemma lem3642595 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term17 A B) (h2 : term82 A B u s f t) : term115 A B u f t.
Proof. exact (fun h0 : term100 A B u f t => @lem3642594 A B u s f t h1 h2). Qed.
Lemma lem3642597 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3642598 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term115 A B u f t) = (term87 A B u f t).
Proof. exact (@lem3642597 (term87 A B u f t)). Qed.
Lemma lem3642599 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term17 A B) (h2 : term82 A B u s f t) : term87 A B u f t.
Proof. exact (EQ_MP (@lem3642598 A B u f t) (@lem3642595 A B u s f t h1 h2)). Qed.
Lemma lem3642602 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3642604 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : A -> Prop) : (term100 A B u f t) = (term116 A B u f t).
Proof. exact (@lem3642602 (term87 A B u f t)). Qed.
Lemma lem3642607 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term82 A B u s f t) : term116 A B u f t.
Proof. exact (EQ_MP (@lem3642604 A B u f t) (@lem3642523 A B u s f t h1)). Qed.
Lemma lem3642610 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term17 A B) (h2 : term82 A B u s f t) : False.
Proof. exact (@lem3642607 A B u s f t h2 (@lem3642599 A B u s f t h1 h2)). Qed.
Lemma lem3642611 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term17 A B) (h2 : term82 A B u s f t) : term117.
Proof. exact (fun h0 : ~ False => @lem3642610 A B u s f t h1 h2). Qed.
Lemma lem3642613 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3642614 : term117 = False.
Proof. exact (@lem3642613 False). Qed.
Lemma lem3642616 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term17 A B) (h2 : term82 A B u s f t) : False.
Proof. exact (EQ_MP (@lem3642614) (@lem3642611 A B u s f t h1 h2)). Qed.
Lemma lem3642617 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term17 A B) (h2 : term82 A B u s f t) : (term82 A B u s f t) = False.
Proof. exact (prop_ext (fun h3 : term82 A B u s f t => @lem3642616 A B u s f t h1 h2) (fun h3 : False => @lem3642234 A B u s f t h2)). Qed.
Lemma lem3642618 {A B : Type'} (u : A -> Prop) (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term17 A B) (h2 : term82 A B u s f t) : False.
Proof. exact (EQ_MP (@lem3642617 A B u s f t h1 h2) (@lem3642234 A B u s f t h2)). Qed.
Lemma lem3642619 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term17 A B) (h2 : term15 A B s f t) : False.
Proof. exact (ex_elim (@lem3641651 A B s f t h2) (fun u : A -> Prop => fun h0 : term84 A B s f t u => @lem3642618 A B u s f t h1 h0)). Qed.
Lemma lem3642620 {_87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term17 A B) (h2 : term15 A B s f t) : term22 _87604 B.
Proof. exact (fun h0 : term16 _87604 B => @lem3642619 A B s f t h1 h2). Qed.
Lemma lem3642621 {_87604 B : Type'} : (term22 _87604 B) = (term23 _87604 B).
Proof. exact (@lem69 (term16 _87604 B)). Qed.
Lemma lem3642622 {_87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term17 A B) (h2 : term15 A B s f t) : term23 _87604 B.
Proof. exact (EQ_MP (@lem3642621 _87604 B) (@lem3642620 _87604 A B s f t h1 h2)). Qed.
Lemma lem3642623 {_87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term15 A B s f t) : term26 _87604 A B.
Proof. exact (fun h0 : term17 A B => @lem3642622 _87604 A B s f t h0 h1). Qed.
Lemma lem3642624 {_87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term15 A B s f t) : term29 _87604 A B.
Proof. exact (fun h0 : term16 _87604 A => @lem3642623 _87604 A B s f t h1). Qed.
Lemma lem3642625 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term15 A B s f t) : term31 _87593 _87604 A B.
Proof. exact (fun h0 : term17 _87593 B => @lem3642624 _87604 A B s f t h1). Qed.
Lemma lem3642626 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term15 A B s f t) : term33 _87593 _87604 A B.
Proof. exact (fun h0 : term17 _87593 A => @lem3642625 _87593 _87604 A B s f t h1). Qed.
Lemma lem3642627 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : term35 _87593 _87604 A B s f t.
Proof. exact (fun h0 : term15 A B s f t => @lem3642626 _87593 _87604 A B s f t h0). Qed.
Lemma lem3642632 {_87593 _87604 A B : Type'} (f : A -> B) (t : A -> Prop) : term39 _87593 _87604 A B f t.
Proof. exact (fun s : B -> Prop => @lem3642627 _87593 _87604 A B s f t). Qed.
Lemma lem3642637 {_87593 _87604 A B : Type'} (t : A -> Prop) : term43 _87593 _87604 A B t.
Proof. exact (fun f : A -> B => @lem3642632 _87593 _87604 A B f t). Qed.
Lemma lem3642642 {_87593 _87604 A B : Type'} : term47 _87593 _87604 A B.
Proof. exact (fun t : A -> Prop => @lem3642637 _87593 _87604 A B t). Qed.
Lemma lem3642643 {_87593 _87604 A B : Type'} : term46 _87593 _87604 A B.
Proof. exact (EQ_MP (@lem3641555 _87593 _87604 A B) (@lem3642642 _87593 _87604 A B)). Qed.
Lemma lem3642644 {_87593 _87604 A B : Type'} (t : A -> Prop) : term118 _87593 _87604 A B t.
Proof. exact (@lem3642643 _87593 _87604 A B t). Qed.
Lemma lem3642645 {_87593 _87604 A B : Type'} (t : A -> Prop) : (term118 _87593 _87604 A B t) = (term42 _87593 _87604 A B t).
Proof. exact (eq_refl (term118 _87593 _87604 A B t)). Qed.
Lemma lem3642646 {_87593 _87604 A B : Type'} (t : A -> Prop) : term42 _87593 _87604 A B t.
Proof. exact (EQ_MP (@lem3642645 _87593 _87604 A B t) (@lem3642644 _87593 _87604 A B t)). Qed.
Lemma lem3642647 {_87593 _87604 A B : Type'} (t : A -> Prop) (f : A -> B) : term119 _87593 _87604 A B t f.
Proof. exact (@lem3642646 _87593 _87604 A B t f). Qed.
Lemma lem3642648 {_87593 _87604 A B : Type'} (f : A -> B) (t : A -> Prop) : (term119 _87593 _87604 A B t f) = (term38 _87593 _87604 A B f t).
Proof. exact (eq_refl (term119 _87593 _87604 A B t f)). Qed.
Lemma lem3642649 {_87593 _87604 A B : Type'} (f : A -> B) (t : A -> Prop) : term38 _87593 _87604 A B f t.
Proof. exact (EQ_MP (@lem3642648 _87593 _87604 A B f t) (@lem3642647 _87593 _87604 A B t f)). Qed.
Lemma lem3642650 {_87593 _87604 A B : Type'} (f : A -> B) (t : A -> Prop) (s : B -> Prop) : term120 _87593 _87604 A B f t s.
Proof. exact (@lem3642649 _87593 _87604 A B f t s). Qed.
Lemma lem3642651 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : (term120 _87593 _87604 A B f t s) = (term18 _87593 _87604 A B s f t).
Proof. exact (eq_refl (term120 _87593 _87604 A B f t s)). Qed.
Lemma lem3642652 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : term18 _87593 _87604 A B s f t.
Proof. exact (EQ_MP (@lem3642651 _87593 _87604 A B s f t) (@lem3642650 _87593 _87604 A B f t s)). Qed.
Lemma lem3642654 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : term18 _87593 _87604 A B s f t.
Proof. exact (@lem3641111 _87593 _87604 A B s f t (@lem3642652 _87593 _87604 A B s f t)). Qed.
Lemma lem3642655 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term15 A B s f t) : term32 _87593 _87604 A B.
Proof. exact (@lem3642654 _87593 _87604 A B s f t (@lem3641090 A B s f t h1)). Qed.
Lemma lem3642656 {_87593 _87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term15 A B s f t) : term30 _87593 _87604 A B.
Proof. exact (@lem3642655 _87593 _87604 A B s f t h1 (@lem3641093 _87593 A)). Qed.
Lemma lem3642657 {_87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term15 A B s f t) : term28 _87604 A B.
Proof. exact (@lem3642656 Prop _87604 A B s f t h1 (@lem3641094 Prop B)). Qed.
Lemma lem3642658 {_87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term15 A B s f t) : term25 _87604 A B.
Proof. exact (@lem3642657 _87604 A B s f t h1 (@lem3641091 _87604 A)). Qed.
Lemma lem3642659 {_87604 A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term15 A B s f t) : term22 _87604 B.
Proof. exact (@lem3642658 _87604 A B s f t h1 (@lem3641095 A B)). Qed.
Lemma lem3642660 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term15 A B s f t) : False.
Proof. exact (@lem3642659 Prop A B s f t h1 (@lem3641092 Prop B)). Qed.
Lemma lem3642661 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term15 A B s f t) : (term15 A B s f t) = False.
Proof. exact (prop_ext (fun h2 : term15 A B s f t => @lem3642660 A B s f t h1) (fun h2 : False => @lem3641090 A B s f t h1)). Qed.
Lemma lem3642662 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term15 A B s f t) : False.
Proof. exact (EQ_MP (@lem3642661 A B s f t h1) (@lem3641090 A B s f t h1)). Qed.
Lemma lem3642663 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : term14 A B s f t.
Proof. exact (fun h0 : term15 A B s f t => @lem3642662 A B s f t h0). Qed.
Lemma lem3642664 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : term13 A B s f t.
Proof. exact (EQ_MP (@lem3641089 A B s f t) (@lem3642663 A B s f t)). Qed.
Lemma lem3642668 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term10 A B s f t) = (term11 A B t s f).
Proof. exact (EQ_MP (@lem3641074 A B t s f) (@lem3641073 A B s f t)). Qed.
Lemma lem3642669 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term10 A B s f t) = (term11 A B t s f).
Proof. exact (@lem3642668 A B t s f). Qed.
Lemma lem3642698 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3642699 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term121 A B s f t) = (term122 A B t s f).
Proof. exact (MK_COMB (@lem3642698) (@lem3642669 A B t s f)). Qed.
Lemma lem3642708 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term62 A B t s f) = (term62 A B t s f).
Proof. exact (eq_refl (term62 A B t s f)). Qed.
Lemma lem3642709 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term123 A B t s f) = (term124 A B t s f).
Proof. exact (MK_COMB (@lem3642699 A B t s f) (@lem3642708 A B t s f)). Qed.
Lemma lem3642712 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term124 A B t s f) = (term123 A B t s f).
Proof. exact (SYM (@lem3642709 A B t s f)). Qed.
Lemma lem3642714 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term0 A P Q.
Proof. exact (@lem3641065 A P Q (@lem7401 A P Q)). Qed.
Lemma lem3642715 {A : Type'} (P : type686 A) (Q : type686 A) : term125 A P Q.
Proof. exact (@lem3642714 (A -> Prop) P Q). Qed.
Lemma lem3642716 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : term126 A B t s f.
Proof. exact (@lem3642715 A (term127 A B t s f) (term61 A B t s f)). Qed.
Lemma lem3642717 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term128 A B t s f u) = (term129 A B t s f u).
Proof. exact (eq_refl (term128 A B t s f u)). Qed.
Lemma lem3642718 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3642719 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term130 A B t s f u) = (term131 A B t s f u).
Proof. exact (MK_COMB (@lem3642718) (@lem3642717 A B t s f u)). Qed.
Lemma lem3642720 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term73 A B t s f u) = (term60 A B t s f u).
Proof. exact (eq_refl (term73 A B t s f u)). Qed.
Lemma lem3642721 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term132 A B t s f u) = (term133 A B t s f u).
Proof. exact (MK_COMB (@lem3642719 A B t s f u) (@lem3642720 A B t s f u)). Qed.
Lemma lem3642722 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term134 A B t s f) = (term135 A B t s f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3642721 A B t s f u)). Qed.
Lemma lem3642723 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3642724 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term136 A B t s f) = (term137 A B t s f).
Proof. exact (MK_COMB (@lem3642723 A) (@lem3642722 A B t s f)). Qed.
Lemma lem3642725 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3642726 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term138 A B t s f) = (term139 A B t s f).
Proof. exact (MK_COMB (@lem3642725) (@lem3642724 A B t s f)). Qed.
Lemma lem3642727 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term128 A B t s f u) = (term129 A B t s f u).
Proof. exact (eq_refl (term128 A B t s f u)). Qed.
Lemma lem3642728 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term140 A B t s f) = (term127 A B t s f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3642727 A B t s f u)). Qed.
Lemma lem3642729 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3642730 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term141 A B t s f) = (term11 A B t s f).
Proof. exact (MK_COMB (@lem3642729 A) (@lem3642728 A B t s f)). Qed.
Lemma lem3642731 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3642732 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term142 A B t s f) = (term122 A B t s f).
Proof. exact (MK_COMB (@lem3642731) (@lem3642730 A B t s f)). Qed.
Lemma lem3642733 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term73 A B t s f u) = (term60 A B t s f u).
Proof. exact (eq_refl (term73 A B t s f u)). Qed.
Lemma lem3642734 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term74 A B t s f) = (term61 A B t s f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3642733 A B t s f u)). Qed.
Lemma lem3642735 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3642736 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term75 A B t s f) = (term62 A B t s f).
Proof. exact (MK_COMB (@lem3642735 A) (@lem3642734 A B t s f)). Qed.
Lemma lem3642737 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term143 A B t s f) = (term124 A B t s f).
Proof. exact (MK_COMB (@lem3642732 A B t s f) (@lem3642736 A B t s f)). Qed.
Lemma lem3642738 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term126 A B t s f) = (term144 A B t s f).
Proof. exact (MK_COMB (@lem3642726 A B t s f) (@lem3642737 A B t s f)). Qed.
Lemma lem3642739 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : term144 A B t s f.
Proof. exact (EQ_MP (@lem3642738 A B t s f) (@lem3642716 A B t s f)). Qed.
Lemma lem3642749 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term145 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3642750 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term145 A s t).
Proof. exact (@lem3642749 A s t). Qed.
Lemma lem3642751 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (@SUBSET A u t) = (term145 A u t).
Proof. exact (@lem3642750 A u t). Qed.
Lemma lem3642758 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3642759 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term146 A u t) = (term147 A u t).
Proof. exact (MK_COMB (@lem3642758) (@lem3642751 A u t)). Qed.
Lemma lem3642789 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term148 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3642790 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (s = t) = (term148 B s t).
Proof. exact (@lem3642789 B s t). Qed.
Lemma lem3642791 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (s = (@IMAGE A B f u)) = (term149 A B s f u).
Proof. exact (@lem3642790 B s (@IMAGE A B f u)). Qed.
Lemma lem3642800 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term150 A B u f) = (term150 A B u f).
Proof. exact (eq_refl (term150 A B u f)). Qed.
Lemma lem3642801 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term151 A B s f u) = (term152 A B s f u).
Proof. exact (MK_COMB (@lem3642800 A B u f) (@lem3642791 A B s f u)). Qed.
Lemma lem3642804 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term129 A B t s f u) = (term153 A B t s f u).
Proof. exact (MK_COMB (@lem3642759 A u t) (@lem3642801 A B s f u)). Qed.
Lemma lem3642807 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3642808 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term131 A B t s f u) = (term154 A B t s f u).
Proof. exact (MK_COMB (@lem3642807) (@lem3642804 A B t s f u)). Qed.
Lemma lem3642812 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term145 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3642813 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term145 A s t).
Proof. exact (@lem3642812 A s t). Qed.
Lemma lem3642814 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (@SUBSET A u t) = (term145 A u t).
Proof. exact (@lem3642813 A u t). Qed.
Lemma lem3642821 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3642822 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term146 A u t) = (term147 A u t).
Proof. exact (MK_COMB (@lem3642821) (@lem3642814 A u t)). Qed.
Lemma lem3642826 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term148 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3642827 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (s = t) = (term148 B s t).
Proof. exact (@lem3642826 B s t). Qed.
Lemma lem3642828 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (s = (@IMAGE A B f u)) = (term149 A B s f u).
Proof. exact (@lem3642827 B s (@IMAGE A B f u)). Qed.
Lemma lem3642837 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term60 A B t s f u) = (term155 A B t s f u).
Proof. exact (MK_COMB (@lem3642822 A u t) (@lem3642828 A B s f u)). Qed.
Lemma lem3642840 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term133 A B t s f u) = (term156 A B t s f u).
Proof. exact (MK_COMB (@lem3642808 A B t s f u) (@lem3642837 A B t s f u)). Qed.
Lemma lem3642843 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term135 A B t s f) = (term157 A B t s f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3642840 A B t s f u)). Qed.
Lemma lem3642844 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3642845 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term137 A B t s f) = (term158 A B t s f).
Proof. exact (MK_COMB (@lem3642844 A) (@lem3642843 A B t s f)). Qed.
Lemma lem3642850 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term158 A B t s f) = (term137 A B t s f).
Proof. exact (SYM (@lem3642845 A B t s f)). Qed.
Lemma lem3642866 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3642867 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3642866 A P x). Qed.
Lemma lem3642868 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3642867 A u x). Qed.
Lemma lem3642869 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3642870 {A : Type'} (u : A -> Prop) (x : A) : (term159 A x u) = (term160 A u x).
Proof. exact (MK_COMB (@lem3642869) (@lem3642868 A u x)). Qed.
Lemma lem3642872 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3642873 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3642872 A P x). Qed.
Lemma lem3642874 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3642873 A t x). Qed.
Lemma lem3642875 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) : (term161 A u x t) = (term162 A u t x).
Proof. exact (MK_COMB (@lem3642870 A u x) (@lem3642874 A t x)). Qed.
Lemma lem3642878 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term163 A u t) = (term164 A u t).
Proof. exact (fun_ext (fun x : A => @lem3642875 A u t x)). Qed.
Lemma lem3642879 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3642880 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term145 A u t) = (term1 A u t).
Proof. exact (MK_COMB (@lem3642879 A) (@lem3642878 A u t)). Qed.
Lemma lem3642885 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3642886 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term147 A u t) = (term165 A u t).
Proof. exact (MK_COMB (@lem3642885) (@lem3642880 A u t)). Qed.
Lemma lem3642902 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3642903 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3642902 A P x). Qed.
Lemma lem3642904 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3642903 A u x). Qed.
Lemma lem3642905 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3642906 {A : Type'} (u : A -> Prop) (x : A) : (term166 A x u) = (term167 A u x).
Proof. exact (MK_COMB (@lem3642905) (@lem3642904 A u x)). Qed.
Lemma lem3642908 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3642909 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3642908 A P x). Qed.
Lemma lem3642910 {A : Type'} (u : A -> Prop) (y : A) : (@IN A y u) = (u y).
Proof. exact (@lem3642909 A u y). Qed.
Lemma lem3642911 {A : Type'} (x : A) (u : A -> Prop) (y : A) : (term168 A x y u) = (term169 A x u y).
Proof. exact (MK_COMB (@lem3642906 A u x) (@lem3642910 A u y)). Qed.
Lemma lem3642914 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3642915 {A : Type'} (x : A) (u : A -> Prop) (y : A) : (term170 A x y u) = (term171 A x u y).
Proof. exact (MK_COMB (@lem3642914) (@lem3642911 A x u y)). Qed.
Lemma lem3642922 {A B : Type'} (f : A -> B) (x : A) (y : A) : (((f x) = (f y)) = (x = y)) = (((f x) = (f y)) = (x = y)).
Proof. exact (eq_refl (((f x) = (f y)) = (x = y))). Qed.
Lemma lem3642923 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : A) : (term172 A B u f x y) = (term173 A B u f x y).
Proof. exact (MK_COMB (@lem3642915 A x u y) (@lem3642922 A B f x y)). Qed.
Lemma lem3642926 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) : (term174 A B u f x) = (term175 A B u f x).
Proof. exact (fun_ext (fun y : A => @lem3642923 A B u f x y)). Qed.
Lemma lem3642927 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3642928 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) : (term176 A B u f x) = (term177 A B u f x).
Proof. exact (MK_COMB (@lem3642927 A) (@lem3642926 A B u f x)). Qed.
Lemma lem3642933 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term178 A B u f) = (term179 A B u f).
Proof. exact (fun_ext (fun x : A => @lem3642928 A B u f x)). Qed.
Lemma lem3642934 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3642935 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term180 A B u f) = (term181 A B u f).
Proof. exact (MK_COMB (@lem3642934 A) (@lem3642933 A B u f)). Qed.
Lemma lem3642940 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3642941 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term150 A B u f) = (term182 A B u f).
Proof. exact (MK_COMB (@lem3642940) (@lem3642935 A B u f)). Qed.
Lemma lem3642949 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3642950 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem3642949 B P x). Qed.
Lemma lem3642951 {B : Type'} (s : B -> Prop) (x : B) : (@IN B x s) = (s x).
Proof. exact (@lem3642950 B s x). Qed.
Lemma lem3642952 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3642953 {B : Type'} (s : B -> Prop) (x : B) : (term183 B x s) = (term184 B s x).
Proof. exact (MK_COMB (@lem3642952) (@lem3642951 B s x)). Qed.
Lemma lem3642955 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term185 A B y f s) = (term186 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3642956 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term185 A B y f s) = (term186 A B y f s).
Proof. exact (@lem3642955 A B y f s). Qed.
Lemma lem3642957 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) : (term185 A B x f u) = (term186 A B x f u).
Proof. exact (@lem3642956 A B x f u). Qed.
Lemma lem3642967 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3642968 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3642967 A P x). Qed.
Lemma lem3642969 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3642968 A u x). Qed.
Lemma lem3642970 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term187 A B x f x') = (term187 A B x f x').
Proof. exact (eq_refl (term187 A B x f x')). Qed.
Lemma lem3642971 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term188 A B x f x' u) = (term189 A B x f u x').
Proof. exact (MK_COMB (@lem3642970 A B x f x') (@lem3642969 A u x')). Qed.
Lemma lem3642974 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) : (term190 A B x f u) = (term191 A B x f u).
Proof. exact (fun_ext (fun x' : A => @lem3642971 A B x f u x')). Qed.
Lemma lem3642975 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3642976 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) : (term186 A B x f u) = (term192 A B x f u).
Proof. exact (MK_COMB (@lem3642975 A) (@lem3642974 A B x f u)). Qed.
Lemma lem3642981 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) : (term185 A B x f u) = (term192 A B x f u).
Proof. exact (TRANS (@lem3642957 A B x f u) (@lem3642976 A B x f u)). Qed.
Lemma lem3642982 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : ((@IN B x s) = (term185 A B x f u)) = ((s x) = (term192 A B x f u)).
Proof. exact (MK_COMB (@lem3642953 B s x) (@lem3642981 A B x f u)). Qed.
Lemma lem3642985 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term193 A B s f u) = (term194 A B s f u).
Proof. exact (fun_ext (fun x : B => @lem3642982 A B s x f u)). Qed.
Lemma lem3642986 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3642987 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term149 A B s f u) = (term195 A B s f u).
Proof. exact (MK_COMB (@lem3642986 B) (@lem3642985 A B s f u)). Qed.
Lemma lem3642992 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term152 A B s f u) = (term196 A B s f u).
Proof. exact (MK_COMB (@lem3642941 A B u f) (@lem3642987 A B s f u)). Qed.
Lemma lem3642995 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term153 A B t s f u) = (term197 A B t s f u).
Proof. exact (MK_COMB (@lem3642886 A u t) (@lem3642992 A B s f u)). Qed.
Lemma lem3642998 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3642999 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term154 A B t s f u) = (term198 A B t s f u).
Proof. exact (MK_COMB (@lem3642998) (@lem3642995 A B t s f u)). Qed.
Lemma lem3643009 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3643010 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3643009 A P x). Qed.
Lemma lem3643011 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3643010 A u x). Qed.
Lemma lem3643012 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3643013 {A : Type'} (u : A -> Prop) (x : A) : (term159 A x u) = (term160 A u x).
Proof. exact (MK_COMB (@lem3643012) (@lem3643011 A u x)). Qed.
Lemma lem3643015 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3643016 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3643015 A P x). Qed.
Lemma lem3643017 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3643016 A t x). Qed.
Lemma lem3643018 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) : (term161 A u x t) = (term162 A u t x).
Proof. exact (MK_COMB (@lem3643013 A u x) (@lem3643017 A t x)). Qed.
Lemma lem3643021 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term163 A u t) = (term164 A u t).
Proof. exact (fun_ext (fun x : A => @lem3643018 A u t x)). Qed.
Lemma lem3643022 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3643023 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term145 A u t) = (term1 A u t).
Proof. exact (MK_COMB (@lem3643022 A) (@lem3643021 A u t)). Qed.
Lemma lem3643028 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3643029 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term147 A u t) = (term165 A u t).
Proof. exact (MK_COMB (@lem3643028) (@lem3643023 A u t)). Qed.
Lemma lem3643037 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3643038 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem3643037 B P x). Qed.
Lemma lem3643039 {B : Type'} (s : B -> Prop) (x : B) : (@IN B x s) = (s x).
Proof. exact (@lem3643038 B s x). Qed.
Lemma lem3643040 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3643041 {B : Type'} (s : B -> Prop) (x : B) : (term183 B x s) = (term184 B s x).
Proof. exact (MK_COMB (@lem3643040) (@lem3643039 B s x)). Qed.
Lemma lem3643043 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term185 A B y f s) = (term186 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3643044 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term185 A B y f s) = (term186 A B y f s).
Proof. exact (@lem3643043 A B y f s). Qed.
Lemma lem3643045 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) : (term185 A B x f u) = (term186 A B x f u).
Proof. exact (@lem3643044 A B x f u). Qed.
Lemma lem3643055 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3643056 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3643055 A P x). Qed.
Lemma lem3643057 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3643056 A u x). Qed.
Lemma lem3643058 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term187 A B x f x') = (term187 A B x f x').
Proof. exact (eq_refl (term187 A B x f x')). Qed.
Lemma lem3643059 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term188 A B x f x' u) = (term189 A B x f u x').
Proof. exact (MK_COMB (@lem3643058 A B x f x') (@lem3643057 A u x')). Qed.
Lemma lem3643062 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) : (term190 A B x f u) = (term191 A B x f u).
Proof. exact (fun_ext (fun x' : A => @lem3643059 A B x f u x')). Qed.
Lemma lem3643063 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3643064 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) : (term186 A B x f u) = (term192 A B x f u).
Proof. exact (MK_COMB (@lem3643063 A) (@lem3643062 A B x f u)). Qed.
Lemma lem3643069 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) : (term185 A B x f u) = (term192 A B x f u).
Proof. exact (TRANS (@lem3643045 A B x f u) (@lem3643064 A B x f u)). Qed.
Lemma lem3643070 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : ((@IN B x s) = (term185 A B x f u)) = ((s x) = (term192 A B x f u)).
Proof. exact (MK_COMB (@lem3643041 B s x) (@lem3643069 A B x f u)). Qed.
Lemma lem3643073 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term193 A B s f u) = (term194 A B s f u).
Proof. exact (fun_ext (fun x : B => @lem3643070 A B s x f u)). Qed.
Lemma lem3643074 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3643075 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term149 A B s f u) = (term195 A B s f u).
Proof. exact (MK_COMB (@lem3643074 B) (@lem3643073 A B s f u)). Qed.
Lemma lem3643080 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term155 A B t s f u) = (term199 A B t s f u).
Proof. exact (MK_COMB (@lem3643029 A u t) (@lem3643075 A B s f u)). Qed.
Lemma lem3643083 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term156 A B t s f u) = (term200 A B t s f u).
Proof. exact (MK_COMB (@lem3642999 A B t s f u) (@lem3643080 A B t s f u)). Qed.
Lemma lem3643086 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term157 A B t s f) = (term201 A B t s f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3643083 A B t s f u)). Qed.
Lemma lem3643087 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3643088 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term158 A B t s f) = (term202 A B t s f).
Proof. exact (MK_COMB (@lem3643087 A) (@lem3643086 A B t s f)). Qed.
Lemma lem3643093 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term202 A B t s f) = (term158 A B t s f).
Proof. exact (SYM (@lem3643088 A B t s f)). Qed.
Lemma lem3643095 (p : Prop) : p = (term12 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3643096 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term202 A B t s f) = (term203 A B t s f).
Proof. exact (@lem3643095 (term202 A B t s f)). Qed.
Lemma lem3643097 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term203 A B t s f) = (term202 A B t s f).
Proof. exact (SYM (@lem3643096 A B t s f)). Qed.
Lemma lem3643098 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (h1 : term204 A B t s f) : term204 A B t s f.
Proof. exact (h1). Qed.
Lemma lem3643101 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (h1 : term203 A B t s f) : term203 A B t s f.
Proof. exact (h1). Qed.
Lemma lem3643102 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : term205 A B t s f.
Proof. exact (fun h0 : term203 A B t s f => @lem3643101 A B t s f h0). Qed.
Lemma lem3643103 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (h1 : term205 A B t s f) : term205 A B t s f.
Proof. exact (h1). Qed.
Lemma lem3643104 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (h1 : term203 A B t s f) : term203 A B t s f.
Proof. exact (h1). Qed.
Lemma lem3643105 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (h1 : term203 A B t s f) (h2 : term205 A B t s f) : term203 A B t s f.
Proof. exact (@lem3643103 A B t s f h2 (@lem3643104 A B t s f h1)). Qed.
Lemma lem3643106 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (h1 : term203 A B t s f) : term206 A B t s f.
Proof. exact (fun h0 : term205 A B t s f => @lem3643105 A B t s f h1 h0). Qed.
Lemma lem3643107 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (h1 : term205 A B t s f) : term205 A B t s f.
Proof. exact (h1). Qed.
Lemma lem3643108 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (h1 : term203 A B t s f) (h2 : term205 A B t s f) : term203 A B t s f.
Proof. exact (@lem3643106 A B t s f h1 (@lem3643107 A B t s f h2)). Qed.
Lemma lem3643109 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (h1 : term205 A B t s f) : term205 A B t s f.
Proof. exact (fun h0 : term203 A B t s f => @lem3643108 A B t s f h0 h1). Qed.
Lemma lem3643110 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : term207 A B t s f.
Proof. exact (fun h0 : term205 A B t s f => @lem3643109 A B t s f h0). Qed.
Lemma lem3643113 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : term205 A B t s f.
Proof. exact (@lem3643110 A B t s f (@lem3643102 A B t s f)). Qed.
Lemma lem3643114 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : term205 A B t s f.
Proof. exact (@lem3643113 A B t s f). Qed.
Lemma lem3643128 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3643129 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term203 A B t s f) = (term208 A B t s f).
Proof. exact (@lem3643128 (term204 A B t s f)). Qed.
Lemma lem3643131 (t : Prop) : (term111 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3643132 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term208 A B t s f) = (term202 A B t s f).
Proof. exact (@lem3643131 (term202 A B t s f)). Qed.
Lemma lem3643137 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term203 A B t s f) = (term202 A B t s f).
Proof. exact (TRANS (@lem3643129 A B t s f) (@lem3643132 A B t s f)). Qed.
Lemma lem3643246 {A B : Type'} (s : B -> Prop) (f : A -> B) : (term209 A B s f) = (term210 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3643137 A B t s f)). Qed.
Lemma lem3643247 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3643248 {A B : Type'} (s : B -> Prop) (f : A -> B) : (term211 A B s f) = (term212 A B s f).
Proof. exact (MK_COMB (@lem3643247 A) (@lem3643246 A B s f)). Qed.
Lemma lem3643253 {A B : Type'} (f : A -> B) : (term213 A B f) = (term214 A B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3643248 A B s f)). Qed.
Lemma lem3643254 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3643255 {A B : Type'} (f : A -> B) : (term215 A B f) = (term216 A B f).
Proof. exact (MK_COMB (@lem3643254 B) (@lem3643253 A B f)). Qed.
Lemma lem3643260 {A B : Type'} : (term217 A B) = (term218 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3643255 A B f)). Qed.
Lemma lem3643261 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3643270 {A B : Type'} : (term219 A B) = (term220 A B).
Proof. exact (MK_COMB (@lem3643261 A B) (@lem3643260 A B)). Qed.
Lemma lem3643275 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term189 A B x f u x') = (term189 A B x f u x').
Proof. exact (eq_refl (term189 A B x f u x')). Qed.
Lemma lem3643276 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) : (term191 A B x f u) = (term191 A B x f u).
Proof. exact (fun_ext (fun x' : A => @lem3643275 A B x f u x')). Qed.
Lemma lem3643277 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3643278 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) : (term192 A B x f u) = (term192 A B x f u).
Proof. exact (MK_COMB (@lem3643277 A) (@lem3643276 A B x f u)). Qed.
Lemma lem3643281 {B : Type'} (s : B -> Prop) (x : B) : (term184 B s x) = (term184 B s x).
Proof. exact (eq_refl (term184 B s x)). Qed.
Lemma lem3643282 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : ((s x) = (term192 A B x f u)) = ((s x) = (term192 A B x f u)).
Proof. exact (MK_COMB (@lem3643281 B s x) (@lem3643278 A B x f u)). Qed.
Lemma lem3643283 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term194 A B s f u) = (term194 A B s f u).
Proof. exact (fun_ext (fun x : B => @lem3643282 A B s x f u)). Qed.
Lemma lem3643284 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3643285 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term195 A B s f u) = (term195 A B s f u).
Proof. exact (MK_COMB (@lem3643284 B) (@lem3643283 A B s f u)). Qed.
Lemma lem3643290 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) : (term162 A u t x) = (term162 A u t x).
Proof. exact (eq_refl (term162 A u t x)). Qed.
Lemma lem3643291 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term164 A u t) = (term164 A u t).
Proof. exact (fun_ext (fun x : A => @lem3643290 A u t x)). Qed.
Lemma lem3643292 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3643293 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term1 A u t) = (term1 A u t).
Proof. exact (MK_COMB (@lem3643292 A) (@lem3643291 A u t)). Qed.
Lemma lem3643294 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3643295 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term165 A u t) = (term165 A u t).
Proof. exact (MK_COMB (@lem3643294) (@lem3643293 A u t)). Qed.
Lemma lem3643296 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term199 A B t s f u) = (term199 A B t s f u).
Proof. exact (MK_COMB (@lem3643295 A u t) (@lem3643285 A B s f u)). Qed.
Lemma lem3643301 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term189 A B x f u x') = (term189 A B x f u x').
Proof. exact (eq_refl (term189 A B x f u x')). Qed.
Lemma lem3643302 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) : (term191 A B x f u) = (term191 A B x f u).
Proof. exact (fun_ext (fun x' : A => @lem3643301 A B x f u x')). Qed.
Lemma lem3643303 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3643304 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) : (term192 A B x f u) = (term192 A B x f u).
Proof. exact (MK_COMB (@lem3643303 A) (@lem3643302 A B x f u)). Qed.
Lemma lem3643307 {B : Type'} (s : B -> Prop) (x : B) : (term184 B s x) = (term184 B s x).
Proof. exact (eq_refl (term184 B s x)). Qed.
Lemma lem3643308 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : ((s x) = (term192 A B x f u)) = ((s x) = (term192 A B x f u)).
Proof. exact (MK_COMB (@lem3643307 B s x) (@lem3643304 A B x f u)). Qed.
Lemma lem3643309 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term194 A B s f u) = (term194 A B s f u).
Proof. exact (fun_ext (fun x : B => @lem3643308 A B s x f u)). Qed.
Lemma lem3643310 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3643311 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term195 A B s f u) = (term195 A B s f u).
Proof. exact (MK_COMB (@lem3643310 B) (@lem3643309 A B s f u)). Qed.
Lemma lem3643324 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : A) : (term173 A B u f x y) = (term173 A B u f x y).
Proof. exact (eq_refl (term173 A B u f x y)). Qed.
Lemma lem3643325 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) : (term175 A B u f x) = (term175 A B u f x).
Proof. exact (fun_ext (fun y : A => @lem3643324 A B u f x y)). Qed.
Lemma lem3643326 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3643327 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) : (term177 A B u f x) = (term177 A B u f x).
Proof. exact (MK_COMB (@lem3643326 A) (@lem3643325 A B u f x)). Qed.
Lemma lem3643328 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term179 A B u f) = (term179 A B u f).
Proof. exact (fun_ext (fun x : A => @lem3643327 A B u f x)). Qed.
Lemma lem3643329 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3643330 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term181 A B u f) = (term181 A B u f).
Proof. exact (MK_COMB (@lem3643329 A) (@lem3643328 A B u f)). Qed.
Lemma lem3643331 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3643332 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term182 A B u f) = (term182 A B u f).
Proof. exact (MK_COMB (@lem3643331) (@lem3643330 A B u f)). Qed.
Lemma lem3643333 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term196 A B s f u) = (term196 A B s f u).
Proof. exact (MK_COMB (@lem3643332 A B u f) (@lem3643311 A B s f u)). Qed.
Lemma lem3643338 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) : (term162 A u t x) = (term162 A u t x).
Proof. exact (eq_refl (term162 A u t x)). Qed.
Lemma lem3643339 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term164 A u t) = (term164 A u t).
Proof. exact (fun_ext (fun x : A => @lem3643338 A u t x)). Qed.
Lemma lem3643340 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3643341 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term1 A u t) = (term1 A u t).
Proof. exact (MK_COMB (@lem3643340 A) (@lem3643339 A u t)). Qed.
Lemma lem3643342 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3643343 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term165 A u t) = (term165 A u t).
Proof. exact (MK_COMB (@lem3643342) (@lem3643341 A u t)). Qed.
Lemma lem3643344 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term197 A B t s f u) = (term197 A B t s f u).
Proof. exact (MK_COMB (@lem3643343 A u t) (@lem3643333 A B s f u)). Qed.
Lemma lem3643345 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3643346 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term198 A B t s f u) = (term198 A B t s f u).
Proof. exact (MK_COMB (@lem3643345) (@lem3643344 A B t s f u)). Qed.
Lemma lem3643347 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term200 A B t s f u) = (term200 A B t s f u).
Proof. exact (MK_COMB (@lem3643346 A B t s f u) (@lem3643296 A B t s f u)). Qed.
Lemma lem3643348 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term201 A B t s f) = (term201 A B t s f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3643347 A B t s f u)). Qed.
Lemma lem3643349 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3643350 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term202 A B t s f) = (term202 A B t s f).
Proof. exact (MK_COMB (@lem3643349 A) (@lem3643348 A B t s f)). Qed.
Lemma lem3643351 {A B : Type'} (s : B -> Prop) (f : A -> B) : (term210 A B s f) = (term210 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3643350 A B t s f)). Qed.
Lemma lem3643352 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3643353 {A B : Type'} (s : B -> Prop) (f : A -> B) : (term212 A B s f) = (term212 A B s f).
Proof. exact (MK_COMB (@lem3643352 A) (@lem3643351 A B s f)). Qed.
Lemma lem3643354 {A B : Type'} (f : A -> B) : (term214 A B f) = (term214 A B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3643353 A B s f)). Qed.
Lemma lem3643355 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3643356 {A B : Type'} (f : A -> B) : (term216 A B f) = (term216 A B f).
Proof. exact (MK_COMB (@lem3643355 B) (@lem3643354 A B f)). Qed.
Lemma lem3643357 {A B : Type'} : (term218 A B) = (term218 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3643356 A B f)). Qed.
Lemma lem3643358 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3643359 {A B : Type'} : (term220 A B) = (term220 A B).
Proof. exact (MK_COMB (@lem3643358 A B) (@lem3643357 A B)). Qed.
Lemma lem3643454 {A B : Type'} : (term219 A B) = (term220 A B).
Proof. exact (TRANS (@lem3643270 A B) (@lem3643359 A B)). Qed.
Lemma lem3643455 {A B : Type'} : (term220 A B) = (term219 A B).
Proof. exact (SYM (@lem3643454 A B)). Qed.
Lemma lem3643456 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (h1 : term197 A B t s f u) : term197 A B t s f u.
Proof. exact (h1). Qed.
Lemma lem3643458 (p : Prop) : p = (term12 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3643459 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term199 A B t s f u) = (term221 A B t s f u).
Proof. exact (@lem3643458 (term199 A B t s f u)). Qed.
Lemma lem3643460 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term221 A B t s f u) = (term199 A B t s f u).
Proof. exact (SYM (@lem3643459 A B t s f u)). Qed.
Lemma lem3643461 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (h1 : term222 A B t s f u) : term222 A B t s f u.
Proof. exact (h1). Qed.
Lemma lem3643468 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) : (term162 A u t x) = (term223 A u t x).
Proof. exact (@lem17265 (u x) (t x)). Qed.
Lemma lem3643469 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term164 A u t) = (term224 A u t).
Proof. exact (fun_ext (fun x : A => @lem3643468 A u t x)). Qed.
Lemma lem3643470 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3643471 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term1 A u t) = (term225 A u t).
Proof. exact (MK_COMB (@lem3643470 A) (@lem3643469 A u t)). Qed.
Lemma lem3643478 {A : Type'} (x : A) (u : A -> Prop) (y : A) : (term226 A x u y) = (term227 A x u y).
Proof. exact (@lem17045 (u x) (u y)). Qed.
Lemma lem3643493 {A B : Type'} (f : A -> B) (x : A) (y : A) : (((f x) = (f y)) = (x = y)) = (term228 A B f x y).
Proof. exact (@lem17784 ((f x) = (f y)) (x = y)). Qed.
Lemma lem3643494 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3643495 {A : Type'} (x : A) (u : A -> Prop) (y : A) : (term229 A x u y) = (term230 A x u y).
Proof. exact (MK_COMB (@lem3643494) (@lem3643478 A x u y)). Qed.
Lemma lem3643496 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : A) : (term231 A B u f x y) = (term232 A B u f x y).
Proof. exact (MK_COMB (@lem3643495 A x u y) (@lem3643493 A B f x y)). Qed.
Lemma lem3643497 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : A) : (term173 A B u f x y) = (term231 A B u f x y).
Proof. exact (@lem17265 (term169 A x u y) (((f x) = (f y)) = (x = y))). Qed.
Lemma lem3643498 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : A) : (term173 A B u f x y) = (term232 A B u f x y).
Proof. exact (TRANS (@lem3643497 A B u f x y) (@lem3643496 A B u f x y)). Qed.
Lemma lem3643499 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) : (term175 A B u f x) = (term233 A B u f x).
Proof. exact (fun_ext (fun y : A => @lem3643498 A B u f x y)). Qed.
Lemma lem3643500 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3643501 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) : (term177 A B u f x) = (term234 A B u f x).
Proof. exact (MK_COMB (@lem3643500 A) (@lem3643499 A B u f x)). Qed.
Lemma lem3643502 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term179 A B u f) = (term235 A B u f).
Proof. exact (fun_ext (fun x : A => @lem3643501 A B u f x)). Qed.
Lemma lem3643503 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3643504 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term181 A B u f) = (term236 A B u f).
Proof. exact (MK_COMB (@lem3643503 A) (@lem3643502 A B u f)). Qed.
Lemma lem3643515 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term237 A B x f u x') = (term238 A B x f u x').
Proof. exact (@lem17045 (x = (f x')) (u x')). Qed.
Lemma lem3643518 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term189 A B x f u x') = (term189 A B x f u x').
Proof. exact (eq_refl (term189 A B x f u x')). Qed.
Lemma lem3643519 {A : Type'} (P : A -> Prop) : (term239 A P) = (term240 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3643520 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) : (term241 A B x f u) = (term242 A B x f u).
Proof. exact (@lem3643519 A (term191 A B x f u)). Qed.
Lemma lem3643521 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term243 A B x f u x') = (term189 A B x f u x').
Proof. exact (eq_refl (term243 A B x f u x')). Qed.
Lemma lem3643522 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3643523 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term244 A B x f u x') = (term237 A B x f u x').
Proof. exact (MK_COMB (@lem3643522) (@lem3643521 A B x f u x')). Qed.
Lemma lem3643524 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term244 A B x f u x') = (term238 A B x f u x').
Proof. exact (TRANS (@lem3643523 A B x f u x') (@lem3643515 A B x f u x')). Qed.
Lemma lem3643525 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) : (term245 A B x f u) = (term246 A B x f u).
Proof. exact (fun_ext (fun x' : A => @lem3643524 A B x f u x')). Qed.
Lemma lem3643526 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3643527 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) : (term242 A B x f u) = (term247 A B x f u).
Proof. exact (MK_COMB (@lem3643526 A) (@lem3643525 A B x f u)). Qed.
Lemma lem3643528 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) : (term241 A B x f u) = (term247 A B x f u).
Proof. exact (TRANS (@lem3643520 A B x f u) (@lem3643527 A B x f u)). Qed.
Lemma lem3643529 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) : (term191 A B x f u) = (term191 A B x f u).
Proof. exact (fun_ext (fun x' : A => @lem3643518 A B x f u x')). Qed.
Lemma lem3643530 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3643531 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) : (term192 A B x f u) = (term192 A B x f u).
Proof. exact (MK_COMB (@lem3643530 A) (@lem3643529 A B x f u)). Qed.
Lemma lem3643533 {B : Type'} (s : B -> Prop) (x : B) : (term248 B s x) = (term248 B s x).
Proof. exact (eq_refl (term248 B s x)). Qed.
Lemma lem3643534 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term249 A B s x f u) = (term249 A B s x f u).
Proof. exact (MK_COMB (@lem3643533 B s x) (@lem3643531 A B x f u)). Qed.
Lemma lem3643536 {B : Type'} (s : B -> Prop) (x : B) : (term250 B s x) = (term250 B s x).
Proof. exact (eq_refl (term250 B s x)). Qed.
Lemma lem3643537 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term251 A B s x f u) = (term252 A B s x f u).
Proof. exact (MK_COMB (@lem3643536 B s x) (@lem3643528 A B x f u)). Qed.
Lemma lem3643538 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3643539 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term253 A B s x f u) = (term254 A B s x f u).
Proof. exact (MK_COMB (@lem3643538) (@lem3643537 A B s x f u)). Qed.
Lemma lem3643540 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term255 A B s x f u) = (term256 A B s x f u).
Proof. exact (MK_COMB (@lem3643539 A B s x f u) (@lem3643534 A B s x f u)). Qed.
Lemma lem3643541 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : ((s x) = (term192 A B x f u)) = (term255 A B s x f u).
Proof. exact (@lem17784 (s x) (term192 A B x f u)). Qed.
Lemma lem3643542 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : ((s x) = (term192 A B x f u)) = (term256 A B s x f u).
Proof. exact (TRANS (@lem3643541 A B s x f u) (@lem3643540 A B s x f u)). Qed.
Lemma lem3643543 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term194 A B s f u) = (term257 A B s f u).
Proof. exact (fun_ext (fun x : B => @lem3643542 A B s x f u)). Qed.
Lemma lem3643544 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3643545 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term195 A B s f u) = (term258 A B s f u).
Proof. exact (MK_COMB (@lem3643544 B) (@lem3643543 A B s f u)). Qed.
Lemma lem3643546 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3643547 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term182 A B u f) = (term259 A B u f).
Proof. exact (MK_COMB (@lem3643546) (@lem3643504 A B u f)). Qed.
Lemma lem3643548 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term196 A B s f u) = (term260 A B s f u).
Proof. exact (MK_COMB (@lem3643547 A B u f) (@lem3643545 A B s f u)). Qed.
Lemma lem3643549 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3643550 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term165 A u t) = (term261 A u t).
Proof. exact (MK_COMB (@lem3643549) (@lem3643471 A u t)). Qed.
Lemma lem3643551 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term197 A B t s f u) = (term262 A B t s f u).
Proof. exact (MK_COMB (@lem3643550 A u t) (@lem3643548 A B s f u)). Qed.
Lemma lem3643637 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term263 A P Q) = (term264 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3643638 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term263 B P Q) = (term264 B P Q).
Proof. exact (@lem3643637 B P Q). Qed.
Lemma lem3643639 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term265 A B s f u) = (term266 A B s f u).
Proof. exact (@lem3643638 B (term267 A B s f u) (term268 A B s f u)). Qed.
Lemma lem3643640 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term269 A B s f u x) = (term252 A B s x f u).
Proof. exact (eq_refl (term269 A B s f u x)). Qed.
Lemma lem3643641 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3643642 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term270 A B s f u x) = (term254 A B s x f u).
Proof. exact (MK_COMB (@lem3643641) (@lem3643640 A B s x f u)). Qed.
Lemma lem3643643 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term271 A B s f u x) = (term249 A B s x f u).
Proof. exact (eq_refl (term271 A B s f u x)). Qed.
Lemma lem3643644 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term272 A B s f u x) = (term256 A B s x f u).
Proof. exact (MK_COMB (@lem3643642 A B s x f u) (@lem3643643 A B s x f u)). Qed.
Lemma lem3643645 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term273 A B s f u) = (term257 A B s f u).
Proof. exact (fun_ext (fun x : B => @lem3643644 A B s x f u)). Qed.
Lemma lem3643646 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3643647 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term265 A B s f u) = (term258 A B s f u).
Proof. exact (MK_COMB (@lem3643646 B) (@lem3643645 A B s f u)). Qed.
Lemma lem3643648 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3643649 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term274 A B s f u) = (term275 A B s f u).
Proof. exact (MK_COMB (@lem3643648) (@lem3643647 A B s f u)). Qed.
Lemma lem3643650 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term269 A B s f u x) = (term252 A B s x f u).
Proof. exact (eq_refl (term269 A B s f u x)). Qed.
Lemma lem3643651 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term276 A B s f u) = (term267 A B s f u).
Proof. exact (fun_ext (fun x : B => @lem3643650 A B s x f u)). Qed.
Lemma lem3643652 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3643653 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term277 A B s f u) = (term278 A B s f u).
Proof. exact (MK_COMB (@lem3643652 B) (@lem3643651 A B s f u)). Qed.
Lemma lem3643654 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3643655 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term279 A B s f u) = (term280 A B s f u).
Proof. exact (MK_COMB (@lem3643654) (@lem3643653 A B s f u)). Qed.
Lemma lem3643656 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term271 A B s f u x) = (term249 A B s x f u).
Proof. exact (eq_refl (term271 A B s f u x)). Qed.
Lemma lem3643657 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term281 A B s f u) = (term268 A B s f u).
Proof. exact (fun_ext (fun x : B => @lem3643656 A B s x f u)). Qed.
Lemma lem3643658 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3643659 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term282 A B s f u) = (term283 A B s f u).
Proof. exact (MK_COMB (@lem3643658 B) (@lem3643657 A B s f u)). Qed.
Lemma lem3643660 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term266 A B s f u) = (term284 A B s f u).
Proof. exact (MK_COMB (@lem3643655 A B s f u) (@lem3643659 A B s f u)). Qed.
Lemma lem3643661 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : ((term265 A B s f u) = (term266 A B s f u)) = ((term258 A B s f u) = (term284 A B s f u)).
Proof. exact (MK_COMB (@lem3643649 A B s f u) (@lem3643660 A B s f u)). Qed.
Lemma lem3643662 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term258 A B s f u) = (term284 A B s f u).
Proof. exact (EQ_MP (@lem3643661 A B s f u) (@lem3643639 A B s f u)). Qed.
Lemma lem3643819 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term259 A B u f) = (term259 A B u f).
Proof. exact (eq_refl (term259 A B u f)). Qed.
Lemma lem3643820 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term260 A B s f u) = (term285 A B s f u).
Proof. exact (MK_COMB (@lem3643819 A B u f) (@lem3643662 A B s f u)). Qed.
Lemma lem3643821 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term261 A u t) = (term261 A u t).
Proof. exact (eq_refl (term261 A u t)). Qed.
Lemma lem3643822 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term262 A B t s f u) = (term286 A B t s f u).
Proof. exact (MK_COMB (@lem3643821 A u t) (@lem3643820 A B s f u)). Qed.
Lemma lem3643824 {A : Type'} (P : Prop) (Q : A -> Prop) : (term287 A P Q) = (term288 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3643825 {A : Type'} (P : Prop) (Q : A -> Prop) : (term287 A P Q) = (term288 A P Q).
Proof. exact (@lem3643824 A P Q). Qed.
Lemma lem3643826 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term289 A B s x f u) = (term290 A B s x f u).
Proof. exact (@lem3643825 A (term291 B s x) (term191 A B x f u)). Qed.
Lemma lem3643827 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term243 A B x f u x') = (term189 A B x f u x').
Proof. exact (eq_refl (term243 A B x f u x')). Qed.
Lemma lem3643828 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) : (term292 A B x f u) = (term191 A B x f u).
Proof. exact (fun_ext (fun x' : A => @lem3643827 A B x f u x')). Qed.
Lemma lem3643829 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3643830 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) : (term293 A B x f u) = (term192 A B x f u).
Proof. exact (MK_COMB (@lem3643829 A) (@lem3643828 A B x f u)). Qed.
Lemma lem3643831 {B : Type'} (s : B -> Prop) (x : B) : (term248 B s x) = (term248 B s x).
Proof. exact (eq_refl (term248 B s x)). Qed.
Lemma lem3643832 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term289 A B s x f u) = (term249 A B s x f u).
Proof. exact (MK_COMB (@lem3643831 B s x) (@lem3643830 A B x f u)). Qed.
Lemma lem3643833 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3643834 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term294 A B s x f u) = (term295 A B s x f u).
Proof. exact (MK_COMB (@lem3643833) (@lem3643832 A B s x f u)). Qed.
Lemma lem3643835 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term243 A B x f u x') = (term189 A B x f u x').
Proof. exact (eq_refl (term243 A B x f u x')). Qed.
Lemma lem3643836 {B : Type'} (s : B -> Prop) (x : B) : (term248 B s x) = (term248 B s x).
Proof. exact (eq_refl (term248 B s x)). Qed.
Lemma lem3643837 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term296 A B s x f u x') = (term297 A B s x f u x').
Proof. exact (MK_COMB (@lem3643836 B s x) (@lem3643835 A B x f u x')). Qed.
Lemma lem3643838 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term298 A B s x f u) = (term299 A B s x f u).
Proof. exact (fun_ext (fun x' : A => @lem3643837 A B s x f u x')). Qed.
Lemma lem3643839 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3643840 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term290 A B s x f u) = (term300 A B s x f u).
Proof. exact (MK_COMB (@lem3643839 A) (@lem3643838 A B s x f u)). Qed.
Lemma lem3643841 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : ((term289 A B s x f u) = (term290 A B s x f u)) = ((term249 A B s x f u) = (term300 A B s x f u)).
Proof. exact (MK_COMB (@lem3643834 A B s x f u) (@lem3643840 A B s x f u)). Qed.
Lemma lem3643842 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term249 A B s x f u) = (term300 A B s x f u).
Proof. exact (EQ_MP (@lem3643841 A B s x f u) (@lem3643826 A B s x f u)). Qed.
Lemma lem3643843 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term268 A B s f u) = (term301 A B s f u).
Proof. exact (fun_ext (fun x : B => @lem3643842 A B s x f u)). Qed.
Lemma lem3643844 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3643845 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term283 A B s f u) = (term302 A B s f u).
Proof. exact (MK_COMB (@lem3643844 B) (@lem3643843 A B s f u)). Qed.
Lemma lem3643847 {A B : Type'} (P : type1413 A B) : (term303 A B P) = (term304 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3643848 {A B : Type'} (P : type1470 A B) : (term305 A B P) = (term306 A B P).
Proof. exact (@lem3643847 B A P). Qed.
Lemma lem3643849 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term307 A B s f u) = (term308 A B s f u).
Proof. exact (@lem3643848 A B (term309 A B s f u)). Qed.
Lemma lem3643850 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term310 A B s f u x) = (term299 A B s x f u).
Proof. exact (eq_refl (term310 A B s f u x)). Qed.
Lemma lem3643851 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3643852 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term311 A B s f u x x') = (term312 A B s x f u x').
Proof. exact (MK_COMB (@lem3643850 A B s x f u) (@lem3643851 A x')). Qed.
Lemma lem3643853 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term312 A B s x f u x') = (term297 A B s x f u x').
Proof. exact (eq_refl (term312 A B s x f u x')). Qed.
Lemma lem3643854 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term311 A B s f u x x') = (term297 A B s x f u x').
Proof. exact (TRANS (@lem3643852 A B s x f u x') (@lem3643853 A B s x f u x')). Qed.
Lemma lem3643855 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term313 A B s f u x) = (term299 A B s x f u).
Proof. exact (fun_ext (fun x' : A => @lem3643854 A B s x f u x')). Qed.
Lemma lem3643856 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3643857 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term314 A B s f u x) = (term300 A B s x f u).
Proof. exact (MK_COMB (@lem3643856 A) (@lem3643855 A B s x f u)). Qed.
Lemma lem3643858 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term315 A B s f u) = (term301 A B s f u).
Proof. exact (fun_ext (fun x : B => @lem3643857 A B s x f u)). Qed.
Lemma lem3643859 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3643860 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term307 A B s f u) = (term302 A B s f u).
Proof. exact (MK_COMB (@lem3643859 B) (@lem3643858 A B s f u)). Qed.
Lemma lem3643861 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3643862 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term316 A B s f u) = (term317 A B s f u).
Proof. exact (MK_COMB (@lem3643861) (@lem3643860 A B s f u)). Qed.
Lemma lem3643863 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term310 A B s f u x) = (term299 A B s x f u).
Proof. exact (eq_refl (term310 A B s f u x)). Qed.
Lemma lem3643864 {A B : Type'} (x : B -> A) (x' : B) : (x x') = (x x').
Proof. exact (eq_refl (x x')). Qed.
Lemma lem3643865 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x : B -> A) (x' : B) : (term318 A B s f u x x') = (term319 A B s f u x x').
Proof. exact (MK_COMB (@lem3643863 A B s x' f u) (@lem3643864 A B x x')). Qed.
Lemma lem3643866 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x : B -> A) (x' : B) : (term319 A B s f u x x') = (term320 A B s f u x x').
Proof. exact (eq_refl (term319 A B s f u x x')). Qed.
Lemma lem3643867 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x : B -> A) (x' : B) : (term318 A B s f u x x') = (term320 A B s f u x x').
Proof. exact (TRANS (@lem3643865 A B s f u x x') (@lem3643866 A B s f u x x')). Qed.
Lemma lem3643868 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x : B -> A) : (term321 A B s f u x) = (term322 A B s f u x).
Proof. exact (fun_ext (fun x' : B => @lem3643867 A B s f u x x')). Qed.
Lemma lem3643869 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3643870 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x : B -> A) : (term323 A B s f u x) = (term324 A B s f u x).
Proof. exact (MK_COMB (@lem3643869 B) (@lem3643868 A B s f u x)). Qed.
Lemma lem3643871 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term325 A B s f u) = (term326 A B s f u).
Proof. exact (fun_ext (fun x : B -> A => @lem3643870 A B s f u x)). Qed.
Lemma lem3643872 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem3643873 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term308 A B s f u) = (term327 A B s f u).
Proof. exact (MK_COMB (@lem3643872 A B) (@lem3643871 A B s f u)). Qed.
Lemma lem3643874 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : ((term307 A B s f u) = (term308 A B s f u)) = ((term302 A B s f u) = (term327 A B s f u)).
Proof. exact (MK_COMB (@lem3643862 A B s f u) (@lem3643873 A B s f u)). Qed.
Lemma lem3643875 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term302 A B s f u) = (term327 A B s f u).
Proof. exact (EQ_MP (@lem3643874 A B s f u) (@lem3643849 A B s f u)). Qed.
Lemma lem3643876 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term283 A B s f u) = (term327 A B s f u).
Proof. exact (TRANS (@lem3643845 A B s f u) (@lem3643875 A B s f u)). Qed.
Lemma lem3643877 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term280 A B s f u) = (term280 A B s f u).
Proof. exact (eq_refl (term280 A B s f u)). Qed.
Lemma lem3643878 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term284 A B s f u) = (term328 A B s f u).
Proof. exact (MK_COMB (@lem3643877 A B s f u) (@lem3643876 A B s f u)). Qed.
Lemma lem3643880 {A : Type'} (P : Prop) (Q : A -> Prop) : (term329 A P Q) = (term330 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3643881 {A B : Type'} (P : Prop) (Q : type805 A B) : (term331 A B P Q) = (term332 A B P Q).
Proof. exact (@lem3643880 (B -> A) P Q). Qed.
Lemma lem3643882 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term333 A B s f u) = (term334 A B s f u).
Proof. exact (@lem3643881 A B (term278 A B s f u) (term326 A B s f u)). Qed.
Lemma lem3643883 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x : B -> A) : (term335 A B s f u x) = (term324 A B s f u x).
Proof. exact (eq_refl (term335 A B s f u x)). Qed.
Lemma lem3643884 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term336 A B s f u) = (term326 A B s f u).
Proof. exact (fun_ext (fun x : B -> A => @lem3643883 A B s f u x)). Qed.
Lemma lem3643885 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem3643886 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term337 A B s f u) = (term327 A B s f u).
Proof. exact (MK_COMB (@lem3643885 A B) (@lem3643884 A B s f u)). Qed.
Lemma lem3643887 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term280 A B s f u) = (term280 A B s f u).
Proof. exact (eq_refl (term280 A B s f u)). Qed.
Lemma lem3643888 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term333 A B s f u) = (term328 A B s f u).
Proof. exact (MK_COMB (@lem3643887 A B s f u) (@lem3643886 A B s f u)). Qed.
Lemma lem3643889 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3643890 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term338 A B s f u) = (term339 A B s f u).
Proof. exact (MK_COMB (@lem3643889) (@lem3643888 A B s f u)). Qed.
Lemma lem3643891 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x : B -> A) : (term335 A B s f u x) = (term324 A B s f u x).
Proof. exact (eq_refl (term335 A B s f u x)). Qed.
Lemma lem3643892 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term280 A B s f u) = (term280 A B s f u).
Proof. exact (eq_refl (term280 A B s f u)). Qed.
Lemma lem3643893 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x : B -> A) : (term340 A B s f u x) = (term341 A B s f u x).
Proof. exact (MK_COMB (@lem3643892 A B s f u) (@lem3643891 A B s f u x)). Qed.
Lemma lem3643894 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term342 A B s f u) = (term343 A B s f u).
Proof. exact (fun_ext (fun x : B -> A => @lem3643893 A B s f u x)). Qed.
Lemma lem3643895 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem3643896 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term334 A B s f u) = (term344 A B s f u).
Proof. exact (MK_COMB (@lem3643895 A B) (@lem3643894 A B s f u)). Qed.
Lemma lem3643897 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : ((term333 A B s f u) = (term334 A B s f u)) = ((term328 A B s f u) = (term344 A B s f u)).
Proof. exact (MK_COMB (@lem3643890 A B s f u) (@lem3643896 A B s f u)). Qed.
Lemma lem3643898 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term328 A B s f u) = (term344 A B s f u).
Proof. exact (EQ_MP (@lem3643897 A B s f u) (@lem3643882 A B s f u)). Qed.
Lemma lem3643899 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term284 A B s f u) = (term344 A B s f u).
Proof. exact (TRANS (@lem3643878 A B s f u) (@lem3643898 A B s f u)). Qed.
Lemma lem3643900 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term259 A B u f) = (term259 A B u f).
Proof. exact (eq_refl (term259 A B u f)). Qed.
Lemma lem3643901 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term285 A B s f u) = (term345 A B s f u).
Proof. exact (MK_COMB (@lem3643900 A B u f) (@lem3643899 A B s f u)). Qed.
Lemma lem3643903 {A : Type'} (P : Prop) (Q : A -> Prop) : (term329 A P Q) = (term330 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3643904 {A B : Type'} (P : Prop) (Q : type805 A B) : (term331 A B P Q) = (term332 A B P Q).
Proof. exact (@lem3643903 (B -> A) P Q). Qed.
Lemma lem3643905 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term346 A B s f u) = (term347 A B s f u).
Proof. exact (@lem3643904 A B (term236 A B u f) (term343 A B s f u)). Qed.
Lemma lem3643906 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x : B -> A) : (term348 A B s f u x) = (term341 A B s f u x).
Proof. exact (eq_refl (term348 A B s f u x)). Qed.
Lemma lem3643907 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term349 A B s f u) = (term343 A B s f u).
Proof. exact (fun_ext (fun x : B -> A => @lem3643906 A B s f u x)). Qed.
Lemma lem3643908 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem3643909 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term350 A B s f u) = (term344 A B s f u).
Proof. exact (MK_COMB (@lem3643908 A B) (@lem3643907 A B s f u)). Qed.
Lemma lem3643910 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term259 A B u f) = (term259 A B u f).
Proof. exact (eq_refl (term259 A B u f)). Qed.
Lemma lem3643911 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term346 A B s f u) = (term345 A B s f u).
Proof. exact (MK_COMB (@lem3643910 A B u f) (@lem3643909 A B s f u)). Qed.
Lemma lem3643912 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3643913 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term351 A B s f u) = (term352 A B s f u).
Proof. exact (MK_COMB (@lem3643912) (@lem3643911 A B s f u)). Qed.
Lemma lem3643914 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x : B -> A) : (term348 A B s f u x) = (term341 A B s f u x).
Proof. exact (eq_refl (term348 A B s f u x)). Qed.
Lemma lem3643915 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term259 A B u f) = (term259 A B u f).
Proof. exact (eq_refl (term259 A B u f)). Qed.
Lemma lem3643916 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x : B -> A) : (term353 A B s f u x) = (term354 A B s f u x).
Proof. exact (MK_COMB (@lem3643915 A B u f) (@lem3643914 A B s f u x)). Qed.
Lemma lem3643917 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term355 A B s f u) = (term356 A B s f u).
Proof. exact (fun_ext (fun x : B -> A => @lem3643916 A B s f u x)). Qed.
Lemma lem3643918 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem3643919 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term347 A B s f u) = (term357 A B s f u).
Proof. exact (MK_COMB (@lem3643918 A B) (@lem3643917 A B s f u)). Qed.
Lemma lem3643920 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : ((term346 A B s f u) = (term347 A B s f u)) = ((term345 A B s f u) = (term357 A B s f u)).
Proof. exact (MK_COMB (@lem3643913 A B s f u) (@lem3643919 A B s f u)). Qed.
Lemma lem3643921 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term345 A B s f u) = (term357 A B s f u).
Proof. exact (EQ_MP (@lem3643920 A B s f u) (@lem3643905 A B s f u)). Qed.
Lemma lem3643922 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term285 A B s f u) = (term357 A B s f u).
Proof. exact (TRANS (@lem3643901 A B s f u) (@lem3643921 A B s f u)). Qed.
Lemma lem3643923 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term261 A u t) = (term261 A u t).
Proof. exact (eq_refl (term261 A u t)). Qed.
Lemma lem3643924 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term286 A B t s f u) = (term358 A B t s f u).
Proof. exact (MK_COMB (@lem3643923 A u t) (@lem3643922 A B s f u)). Qed.
Lemma lem3643926 {A : Type'} (P : Prop) (Q : A -> Prop) : (term329 A P Q) = (term330 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3643927 {A B : Type'} (P : Prop) (Q : type805 A B) : (term331 A B P Q) = (term332 A B P Q).
Proof. exact (@lem3643926 (B -> A) P Q). Qed.
Lemma lem3643928 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term359 A B t s f u) = (term360 A B t s f u).
Proof. exact (@lem3643927 A B (term225 A u t) (term356 A B s f u)). Qed.
Lemma lem3643929 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x : B -> A) : (term361 A B s f u x) = (term354 A B s f u x).
Proof. exact (eq_refl (term361 A B s f u x)). Qed.
Lemma lem3643930 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term362 A B s f u) = (term356 A B s f u).
Proof. exact (fun_ext (fun x : B -> A => @lem3643929 A B s f u x)). Qed.
Lemma lem3643931 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem3643932 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term363 A B s f u) = (term357 A B s f u).
Proof. exact (MK_COMB (@lem3643931 A B) (@lem3643930 A B s f u)). Qed.
Lemma lem3643933 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term261 A u t) = (term261 A u t).
Proof. exact (eq_refl (term261 A u t)). Qed.
Lemma lem3643934 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term359 A B t s f u) = (term358 A B t s f u).
Proof. exact (MK_COMB (@lem3643933 A u t) (@lem3643932 A B s f u)). Qed.
Lemma lem3643935 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3643936 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term364 A B t s f u) = (term365 A B t s f u).
Proof. exact (MK_COMB (@lem3643935) (@lem3643934 A B t s f u)). Qed.
Lemma lem3643937 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x : B -> A) : (term361 A B s f u x) = (term354 A B s f u x).
Proof. exact (eq_refl (term361 A B s f u x)). Qed.
Lemma lem3643938 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term261 A u t) = (term261 A u t).
Proof. exact (eq_refl (term261 A u t)). Qed.
Lemma lem3643939 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x : B -> A) : (term366 A B t s f u x) = (term367 A B t s f u x).
Proof. exact (MK_COMB (@lem3643938 A u t) (@lem3643937 A B s f u x)). Qed.
Lemma lem3643940 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term368 A B t s f u) = (term369 A B t s f u).
Proof. exact (fun_ext (fun x : B -> A => @lem3643939 A B t s f u x)). Qed.
Lemma lem3643941 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem3643942 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term360 A B t s f u) = (term370 A B t s f u).
Proof. exact (MK_COMB (@lem3643941 A B) (@lem3643940 A B t s f u)). Qed.
Lemma lem3643943 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : ((term359 A B t s f u) = (term360 A B t s f u)) = ((term358 A B t s f u) = (term370 A B t s f u)).
Proof. exact (MK_COMB (@lem3643936 A B t s f u) (@lem3643942 A B t s f u)). Qed.
Lemma lem3643944 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term358 A B t s f u) = (term370 A B t s f u).
Proof. exact (EQ_MP (@lem3643943 A B t s f u) (@lem3643928 A B t s f u)). Qed.
Lemma lem3643945 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term286 A B t s f u) = (term370 A B t s f u).
Proof. exact (TRANS (@lem3643924 A B t s f u) (@lem3643944 A B t s f u)). Qed.
Lemma lem3643946 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term262 A B t s f u) = (term370 A B t s f u).
Proof. exact (TRANS (@lem3643822 A B t s f u) (@lem3643945 A B t s f u)). Qed.
Lemma lem3643947 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term197 A B t s f u) = (term370 A B t s f u).
Proof. exact (TRANS (@lem3643551 A B t s f u) (@lem3643946 A B t s f u)). Qed.
Lemma lem3643948 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (h1 : term197 A B t s f u) : term370 A B t s f u.
Proof. exact (EQ_MP (@lem3643947 A B t s f u) (@lem3643456 A B t s f u h1)). Qed.
Lemma lem3643955 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) : (term371 A u t x) = (term372 A u t x).
Proof. exact (@lem17362 (u x) (t x)). Qed.
Lemma lem3643956 {A : Type'} (P : A -> Prop) : (term373 A P) = (term374 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3643957 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term375 A u t) = (term376 A u t).
Proof. exact (@lem3643956 A (term164 A u t)). Qed.
Lemma lem3643958 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) : (term377 A u t x) = (term162 A u t x).
Proof. exact (eq_refl (term377 A u t x)). Qed.
Lemma lem3643959 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3643960 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) : (term378 A u t x) = (term371 A u t x).
Proof. exact (MK_COMB (@lem3643959) (@lem3643958 A u t x)). Qed.
Lemma lem3643961 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) : (term378 A u t x) = (term372 A u t x).
Proof. exact (TRANS (@lem3643960 A u t x) (@lem3643955 A u t x)). Qed.
Lemma lem3643962 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term379 A u t) = (term380 A u t).
Proof. exact (fun_ext (fun x : A => @lem3643961 A u t x)). Qed.
Lemma lem3643963 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3643964 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term376 A u t) = (term381 A u t).
Proof. exact (MK_COMB (@lem3643963 A) (@lem3643962 A u t)). Qed.
Lemma lem3643965 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term375 A u t) = (term381 A u t).
Proof. exact (TRANS (@lem3643957 A u t) (@lem3643964 A u t)). Qed.
Lemma lem3643976 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term237 A B x f u x') = (term238 A B x f u x').
Proof. exact (@lem17045 (x = (f x')) (u x')). Qed.
Lemma lem3643979 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term189 A B x f u x') = (term189 A B x f u x').
Proof. exact (eq_refl (term189 A B x f u x')). Qed.
Lemma lem3643980 {A : Type'} (P : A -> Prop) : (term239 A P) = (term240 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3643981 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) : (term241 A B x f u) = (term242 A B x f u).
Proof. exact (@lem3643980 A (term191 A B x f u)). Qed.
Lemma lem3643982 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term243 A B x f u x') = (term189 A B x f u x').
Proof. exact (eq_refl (term243 A B x f u x')). Qed.
Lemma lem3643983 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3643984 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term244 A B x f u x') = (term237 A B x f u x').
Proof. exact (MK_COMB (@lem3643983) (@lem3643982 A B x f u x')). Qed.
Lemma lem3643985 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term244 A B x f u x') = (term238 A B x f u x').
Proof. exact (TRANS (@lem3643984 A B x f u x') (@lem3643976 A B x f u x')). Qed.
Lemma lem3643986 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) : (term245 A B x f u) = (term246 A B x f u).
Proof. exact (fun_ext (fun x' : A => @lem3643985 A B x f u x')). Qed.
Lemma lem3643987 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3643988 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) : (term242 A B x f u) = (term247 A B x f u).
Proof. exact (MK_COMB (@lem3643987 A) (@lem3643986 A B x f u)). Qed.
Lemma lem3643989 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) : (term241 A B x f u) = (term247 A B x f u).
Proof. exact (TRANS (@lem3643981 A B x f u) (@lem3643988 A B x f u)). Qed.
Lemma lem3643990 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) : (term191 A B x f u) = (term191 A B x f u).
Proof. exact (fun_ext (fun x' : A => @lem3643979 A B x f u x')). Qed.
Lemma lem3643991 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3643992 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) : (term192 A B x f u) = (term192 A B x f u).
Proof. exact (MK_COMB (@lem3643991 A) (@lem3643990 A B x f u)). Qed.
Lemma lem3643994 {B : Type'} (s : B -> Prop) (x : B) : (term382 B s x) = (term382 B s x).
Proof. exact (eq_refl (term382 B s x)). Qed.
Lemma lem3643995 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term383 A B s x f u) = (term383 A B s x f u).
Proof. exact (MK_COMB (@lem3643994 B s x) (@lem3643992 A B x f u)). Qed.
Lemma lem3643997 {B : Type'} (s : B -> Prop) (x : B) : (term167 B s x) = (term167 B s x).
Proof. exact (eq_refl (term167 B s x)). Qed.
Lemma lem3643998 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term384 A B s x f u) = (term385 A B s x f u).
Proof. exact (MK_COMB (@lem3643997 B s x) (@lem3643989 A B x f u)). Qed.
Lemma lem3643999 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3644000 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term386 A B s x f u) = (term387 A B s x f u).
Proof. exact (MK_COMB (@lem3643999) (@lem3643998 A B s x f u)). Qed.
Lemma lem3644001 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term388 A B s x f u) = (term389 A B s x f u).
Proof. exact (MK_COMB (@lem3644000 A B s x f u) (@lem3643995 A B s x f u)). Qed.
Lemma lem3644002 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term390 A B s x f u) = (term388 A B s x f u).
Proof. exact (@lem17646 (s x) (term192 A B x f u)). Qed.
Lemma lem3644003 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term390 A B s x f u) = (term389 A B s x f u).
Proof. exact (TRANS (@lem3644002 A B s x f u) (@lem3644001 A B s x f u)). Qed.
Lemma lem3644004 {B : Type'} (P : B -> Prop) : (term373 B P) = (term374 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem3644005 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term391 A B s f u) = (term392 A B s f u).
Proof. exact (@lem3644004 B (term194 A B s f u)). Qed.
Lemma lem3644006 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term393 A B s f u x) = ((s x) = (term192 A B x f u)).
Proof. exact (eq_refl (term393 A B s f u x)). Qed.
Lemma lem3644007 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3644008 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term394 A B s f u x) = (term390 A B s x f u).
Proof. exact (MK_COMB (@lem3644007) (@lem3644006 A B s x f u)). Qed.
Lemma lem3644009 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term394 A B s f u x) = (term389 A B s x f u).
Proof. exact (TRANS (@lem3644008 A B s x f u) (@lem3644003 A B s x f u)). Qed.
Lemma lem3644010 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term395 A B s f u) = (term396 A B s f u).
Proof. exact (fun_ext (fun x : B => @lem3644009 A B s x f u)). Qed.
Lemma lem3644011 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3644012 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term392 A B s f u) = (term397 A B s f u).
Proof. exact (MK_COMB (@lem3644011 B) (@lem3644010 A B s f u)). Qed.
Lemma lem3644013 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term391 A B s f u) = (term397 A B s f u).
Proof. exact (TRANS (@lem3644005 A B s f u) (@lem3644012 A B s f u)). Qed.
Lemma lem3644014 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3644015 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term398 A u t) = (term399 A u t).
Proof. exact (MK_COMB (@lem3644014) (@lem3643965 A u t)). Qed.
Lemma lem3644016 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term400 A B t s f u) = (term401 A B t s f u).
Proof. exact (MK_COMB (@lem3644015 A u t) (@lem3644013 A B s f u)). Qed.
Lemma lem3644017 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term222 A B t s f u) = (term400 A B t s f u).
Proof. exact (@lem17045 (term1 A u t) (term195 A B s f u)). Qed.
Lemma lem3644018 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term222 A B t s f u) = (term401 A B t s f u).
Proof. exact (TRANS (@lem3644017 A B t s f u) (@lem3644016 A B t s f u)). Qed.
Lemma lem3644048 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term402 A P Q) = (term403 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3644049 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term402 B P Q) = (term403 B P Q).
Proof. exact (@lem3644048 B P Q). Qed.
Lemma lem3644050 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term404 A B s f u) = (term405 A B s f u).
Proof. exact (@lem3644049 B (term406 A B s f u) (term407 A B s f u)). Qed.
Lemma lem3644051 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term408 A B s f u x) = (term385 A B s x f u).
Proof. exact (eq_refl (term408 A B s f u x)). Qed.
Lemma lem3644052 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3644053 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term409 A B s f u x) = (term387 A B s x f u).
Proof. exact (MK_COMB (@lem3644052) (@lem3644051 A B s x f u)). Qed.
Lemma lem3644054 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term410 A B s f u x) = (term383 A B s x f u).
Proof. exact (eq_refl (term410 A B s f u x)). Qed.
Lemma lem3644055 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term411 A B s f u x) = (term389 A B s x f u).
Proof. exact (MK_COMB (@lem3644053 A B s x f u) (@lem3644054 A B s x f u)). Qed.
Lemma lem3644056 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term412 A B s f u) = (term396 A B s f u).
Proof. exact (fun_ext (fun x : B => @lem3644055 A B s x f u)). Qed.
Lemma lem3644057 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3644058 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term404 A B s f u) = (term397 A B s f u).
Proof. exact (MK_COMB (@lem3644057 B) (@lem3644056 A B s f u)). Qed.
Lemma lem3644059 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3644060 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term413 A B s f u) = (term414 A B s f u).
Proof. exact (MK_COMB (@lem3644059) (@lem3644058 A B s f u)). Qed.
Lemma lem3644061 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term408 A B s f u x) = (term385 A B s x f u).
Proof. exact (eq_refl (term408 A B s f u x)). Qed.
Lemma lem3644062 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term415 A B s f u) = (term406 A B s f u).
Proof. exact (fun_ext (fun x : B => @lem3644061 A B s x f u)). Qed.
Lemma lem3644063 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3644064 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term416 A B s f u) = (term417 A B s f u).
Proof. exact (MK_COMB (@lem3644063 B) (@lem3644062 A B s f u)). Qed.
Lemma lem3644065 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3644066 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term418 A B s f u) = (term419 A B s f u).
Proof. exact (MK_COMB (@lem3644065) (@lem3644064 A B s f u)). Qed.
Lemma lem3644067 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term410 A B s f u x) = (term383 A B s x f u).
Proof. exact (eq_refl (term410 A B s f u x)). Qed.
Lemma lem3644068 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term420 A B s f u) = (term407 A B s f u).
Proof. exact (fun_ext (fun x : B => @lem3644067 A B s x f u)). Qed.
Lemma lem3644069 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3644070 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term421 A B s f u) = (term422 A B s f u).
Proof. exact (MK_COMB (@lem3644069 B) (@lem3644068 A B s f u)). Qed.
Lemma lem3644071 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term405 A B s f u) = (term423 A B s f u).
Proof. exact (MK_COMB (@lem3644066 A B s f u) (@lem3644070 A B s f u)). Qed.
Lemma lem3644072 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : ((term404 A B s f u) = (term405 A B s f u)) = ((term397 A B s f u) = (term423 A B s f u)).
Proof. exact (MK_COMB (@lem3644060 A B s f u) (@lem3644071 A B s f u)). Qed.
Lemma lem3644073 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term397 A B s f u) = (term423 A B s f u).
Proof. exact (EQ_MP (@lem3644072 A B s f u) (@lem3644050 A B s f u)). Qed.
Lemma lem3644230 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term399 A u t) = (term399 A u t).
Proof. exact (eq_refl (term399 A u t)). Qed.
Lemma lem3644231 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term401 A B t s f u) = (term424 A B t s f u).
Proof. exact (MK_COMB (@lem3644230 A u t) (@lem3644073 A B s f u)). Qed.
Lemma lem3644233 {A : Type'} (P : Prop) (Q : A -> Prop) : (term329 A P Q) = (term330 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3644234 {A : Type'} (P : Prop) (Q : A -> Prop) : (term329 A P Q) = (term330 A P Q).
Proof. exact (@lem3644233 A P Q). Qed.
Lemma lem3644235 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term425 A B s x f u) = (term426 A B s x f u).
Proof. exact (@lem3644234 A (term291 B s x) (term191 A B x f u)). Qed.
Lemma lem3644236 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term243 A B x f u x') = (term189 A B x f u x').
Proof. exact (eq_refl (term243 A B x f u x')). Qed.
Lemma lem3644237 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) : (term292 A B x f u) = (term191 A B x f u).
Proof. exact (fun_ext (fun x' : A => @lem3644236 A B x f u x')). Qed.
Lemma lem3644238 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3644239 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) : (term293 A B x f u) = (term192 A B x f u).
Proof. exact (MK_COMB (@lem3644238 A) (@lem3644237 A B x f u)). Qed.
Lemma lem3644240 {B : Type'} (s : B -> Prop) (x : B) : (term382 B s x) = (term382 B s x).
Proof. exact (eq_refl (term382 B s x)). Qed.
Lemma lem3644241 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term425 A B s x f u) = (term383 A B s x f u).
Proof. exact (MK_COMB (@lem3644240 B s x) (@lem3644239 A B x f u)). Qed.
Lemma lem3644242 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3644243 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term427 A B s x f u) = (term428 A B s x f u).
Proof. exact (MK_COMB (@lem3644242) (@lem3644241 A B s x f u)). Qed.
Lemma lem3644244 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term243 A B x f u x') = (term189 A B x f u x').
Proof. exact (eq_refl (term243 A B x f u x')). Qed.
Lemma lem3644245 {B : Type'} (s : B -> Prop) (x : B) : (term382 B s x) = (term382 B s x).
Proof. exact (eq_refl (term382 B s x)). Qed.
Lemma lem3644246 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term429 A B s x f u x') = (term430 A B s x f u x').
Proof. exact (MK_COMB (@lem3644245 B s x) (@lem3644244 A B x f u x')). Qed.
Lemma lem3644247 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term431 A B s x f u) = (term432 A B s x f u).
Proof. exact (fun_ext (fun x' : A => @lem3644246 A B s x f u x')). Qed.
Lemma lem3644248 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3644249 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term426 A B s x f u) = (term433 A B s x f u).
Proof. exact (MK_COMB (@lem3644248 A) (@lem3644247 A B s x f u)). Qed.
Lemma lem3644250 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : ((term425 A B s x f u) = (term426 A B s x f u)) = ((term383 A B s x f u) = (term433 A B s x f u)).
Proof. exact (MK_COMB (@lem3644243 A B s x f u) (@lem3644249 A B s x f u)). Qed.
Lemma lem3644251 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term383 A B s x f u) = (term433 A B s x f u).
Proof. exact (EQ_MP (@lem3644250 A B s x f u) (@lem3644235 A B s x f u)). Qed.
Lemma lem3644252 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term407 A B s f u) = (term434 A B s f u).
Proof. exact (fun_ext (fun x : B => @lem3644251 A B s x f u)). Qed.
Lemma lem3644253 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3644254 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term422 A B s f u) = (term435 A B s f u).
Proof. exact (MK_COMB (@lem3644253 B) (@lem3644252 A B s f u)). Qed.
Lemma lem3644255 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term419 A B s f u) = (term419 A B s f u).
Proof. exact (eq_refl (term419 A B s f u)). Qed.
Lemma lem3644256 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term423 A B s f u) = (term436 A B s f u).
Proof. exact (MK_COMB (@lem3644255 A B s f u) (@lem3644254 A B s f u)). Qed.
Lemma lem3644258 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term403 A P Q) = (term402 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3644259 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term403 B P Q) = (term402 B P Q).
Proof. exact (@lem3644258 B P Q). Qed.
Lemma lem3644260 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term437 A B s f u) = (term438 A B s f u).
Proof. exact (@lem3644259 B (term406 A B s f u) (term434 A B s f u)). Qed.
Lemma lem3644261 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term408 A B s f u x) = (term385 A B s x f u).
Proof. exact (eq_refl (term408 A B s f u x)). Qed.
Lemma lem3644262 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term415 A B s f u) = (term406 A B s f u).
Proof. exact (fun_ext (fun x : B => @lem3644261 A B s x f u)). Qed.
Lemma lem3644263 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3644264 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term416 A B s f u) = (term417 A B s f u).
Proof. exact (MK_COMB (@lem3644263 B) (@lem3644262 A B s f u)). Qed.
Lemma lem3644265 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3644266 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term418 A B s f u) = (term419 A B s f u).
Proof. exact (MK_COMB (@lem3644265) (@lem3644264 A B s f u)). Qed.
Lemma lem3644267 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term439 A B s f u x) = (term433 A B s x f u).
Proof. exact (eq_refl (term439 A B s f u x)). Qed.
Lemma lem3644268 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term440 A B s f u) = (term434 A B s f u).
Proof. exact (fun_ext (fun x : B => @lem3644267 A B s x f u)). Qed.
Lemma lem3644269 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3644270 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term441 A B s f u) = (term435 A B s f u).
Proof. exact (MK_COMB (@lem3644269 B) (@lem3644268 A B s f u)). Qed.
Lemma lem3644271 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term437 A B s f u) = (term436 A B s f u).
Proof. exact (MK_COMB (@lem3644266 A B s f u) (@lem3644270 A B s f u)). Qed.
Lemma lem3644272 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3644273 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term442 A B s f u) = (term443 A B s f u).
Proof. exact (MK_COMB (@lem3644272) (@lem3644271 A B s f u)). Qed.
Lemma lem3644274 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term408 A B s f u x) = (term385 A B s x f u).
Proof. exact (eq_refl (term408 A B s f u x)). Qed.
Lemma lem3644275 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3644276 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term409 A B s f u x) = (term387 A B s x f u).
Proof. exact (MK_COMB (@lem3644275) (@lem3644274 A B s x f u)). Qed.
Lemma lem3644277 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term439 A B s f u x) = (term433 A B s x f u).
Proof. exact (eq_refl (term439 A B s f u x)). Qed.
Lemma lem3644278 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term444 A B s f u x) = (term445 A B s x f u).
Proof. exact (MK_COMB (@lem3644276 A B s x f u) (@lem3644277 A B s x f u)). Qed.
Lemma lem3644279 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term446 A B s f u) = (term447 A B s f u).
Proof. exact (fun_ext (fun x : B => @lem3644278 A B s x f u)). Qed.
Lemma lem3644280 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3644281 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term438 A B s f u) = (term448 A B s f u).
Proof. exact (MK_COMB (@lem3644280 B) (@lem3644279 A B s f u)). Qed.
Lemma lem3644282 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : ((term437 A B s f u) = (term438 A B s f u)) = ((term436 A B s f u) = (term448 A B s f u)).
Proof. exact (MK_COMB (@lem3644273 A B s f u) (@lem3644281 A B s f u)). Qed.
Lemma lem3644283 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term436 A B s f u) = (term448 A B s f u).
Proof. exact (EQ_MP (@lem3644282 A B s f u) (@lem3644260 A B s f u)). Qed.
Lemma lem3644285 {A : Type'} (P : Prop) (Q : A -> Prop) : (term287 A P Q) = (term288 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3644286 {A : Type'} (P : Prop) (Q : A -> Prop) : (term287 A P Q) = (term288 A P Q).
Proof. exact (@lem3644285 A P Q). Qed.
Lemma lem3644287 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term449 A B s x f u) = (term450 A B s x f u).
Proof. exact (@lem3644286 A (term385 A B s x f u) (term432 A B s x f u)). Qed.
Lemma lem3644288 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term451 A B s x f u x') = (term430 A B s x f u x').
Proof. exact (eq_refl (term451 A B s x f u x')). Qed.
Lemma lem3644289 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term452 A B s x f u) = (term432 A B s x f u).
Proof. exact (fun_ext (fun x' : A => @lem3644288 A B s x f u x')). Qed.
Lemma lem3644290 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3644291 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term453 A B s x f u) = (term433 A B s x f u).
Proof. exact (MK_COMB (@lem3644290 A) (@lem3644289 A B s x f u)). Qed.
Lemma lem3644292 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term387 A B s x f u) = (term387 A B s x f u).
Proof. exact (eq_refl (term387 A B s x f u)). Qed.
Lemma lem3644293 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term449 A B s x f u) = (term445 A B s x f u).
Proof. exact (MK_COMB (@lem3644292 A B s x f u) (@lem3644291 A B s x f u)). Qed.
Lemma lem3644294 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3644295 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term454 A B s x f u) = (term455 A B s x f u).
Proof. exact (MK_COMB (@lem3644294) (@lem3644293 A B s x f u)). Qed.
Lemma lem3644296 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term451 A B s x f u x') = (term430 A B s x f u x').
Proof. exact (eq_refl (term451 A B s x f u x')). Qed.
Lemma lem3644297 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term387 A B s x f u) = (term387 A B s x f u).
Proof. exact (eq_refl (term387 A B s x f u)). Qed.
Lemma lem3644298 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term456 A B s x f u x') = (term457 A B s x f u x').
Proof. exact (MK_COMB (@lem3644297 A B s x f u) (@lem3644296 A B s x f u x')). Qed.
Lemma lem3644299 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term458 A B s x f u) = (term459 A B s x f u).
Proof. exact (fun_ext (fun x' : A => @lem3644298 A B s x f u x')). Qed.
Lemma lem3644300 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3644301 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term450 A B s x f u) = (term460 A B s x f u).
Proof. exact (MK_COMB (@lem3644300 A) (@lem3644299 A B s x f u)). Qed.
Lemma lem3644302 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : ((term449 A B s x f u) = (term450 A B s x f u)) = ((term445 A B s x f u) = (term460 A B s x f u)).
Proof. exact (MK_COMB (@lem3644295 A B s x f u) (@lem3644301 A B s x f u)). Qed.
Lemma lem3644303 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term445 A B s x f u) = (term460 A B s x f u).
Proof. exact (EQ_MP (@lem3644302 A B s x f u) (@lem3644287 A B s x f u)). Qed.
Lemma lem3644304 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term447 A B s f u) = (term461 A B s f u).
Proof. exact (fun_ext (fun x : B => @lem3644303 A B s x f u)). Qed.
Lemma lem3644305 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3644306 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term448 A B s f u) = (term462 A B s f u).
Proof. exact (MK_COMB (@lem3644305 B) (@lem3644304 A B s f u)). Qed.
Lemma lem3644307 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term436 A B s f u) = (term462 A B s f u).
Proof. exact (TRANS (@lem3644283 A B s f u) (@lem3644306 A B s f u)). Qed.
Lemma lem3644308 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term423 A B s f u) = (term462 A B s f u).
Proof. exact (TRANS (@lem3644256 A B s f u) (@lem3644307 A B s f u)). Qed.
Lemma lem3644309 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term399 A u t) = (term399 A u t).
Proof. exact (eq_refl (term399 A u t)). Qed.
Lemma lem3644310 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term424 A B t s f u) = (term463 A B t s f u).
Proof. exact (MK_COMB (@lem3644309 A u t) (@lem3644308 A B s f u)). Qed.
Lemma lem3644314 {A : Type'} (P : A -> Prop) (Q : Prop) : (term464 A P Q) = (term465 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3644315 {A : Type'} (P : A -> Prop) (Q : Prop) : (term464 A P Q) = (term465 A P Q).
Proof. exact (@lem3644314 A P Q). Qed.
Lemma lem3644316 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term466 A B t s f u) = (term467 A B t s f u).
Proof. exact (@lem3644315 A (term380 A u t) (term462 A B s f u)). Qed.
Lemma lem3644317 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) : (term468 A u t x) = (term372 A u t x).
Proof. exact (eq_refl (term468 A u t x)). Qed.
Lemma lem3644318 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term469 A u t) = (term380 A u t).
Proof. exact (fun_ext (fun x : A => @lem3644317 A u t x)). Qed.
Lemma lem3644319 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3644320 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term470 A u t) = (term381 A u t).
Proof. exact (MK_COMB (@lem3644319 A) (@lem3644318 A u t)). Qed.
Lemma lem3644321 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3644322 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term471 A u t) = (term399 A u t).
Proof. exact (MK_COMB (@lem3644321) (@lem3644320 A u t)). Qed.
Lemma lem3644323 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term462 A B s f u) = (term462 A B s f u).
Proof. exact (eq_refl (term462 A B s f u)). Qed.
Lemma lem3644324 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term466 A B t s f u) = (term463 A B t s f u).
Proof. exact (MK_COMB (@lem3644322 A u t) (@lem3644323 A B s f u)). Qed.
Lemma lem3644325 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3644326 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term472 A B t s f u) = (term473 A B t s f u).
Proof. exact (MK_COMB (@lem3644325) (@lem3644324 A B t s f u)). Qed.
Lemma lem3644327 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) : (term468 A u t x) = (term372 A u t x).
Proof. exact (eq_refl (term468 A u t x)). Qed.
Lemma lem3644328 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3644329 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) : (term474 A u t x) = (term475 A u t x).
Proof. exact (MK_COMB (@lem3644328) (@lem3644327 A u t x)). Qed.
Lemma lem3644330 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term462 A B s f u) = (term462 A B s f u).
Proof. exact (eq_refl (term462 A B s f u)). Qed.
Lemma lem3644331 {A B : Type'} (t : A -> Prop) (x : A) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term476 A B t x s f u) = (term477 A B t x s f u).
Proof. exact (MK_COMB (@lem3644329 A u t x) (@lem3644330 A B s f u)). Qed.
Lemma lem3644332 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term478 A B t s f u) = (term479 A B t s f u).
Proof. exact (fun_ext (fun x : A => @lem3644331 A B t x s f u)). Qed.
Lemma lem3644333 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3644334 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term467 A B t s f u) = (term480 A B t s f u).
Proof. exact (MK_COMB (@lem3644333 A) (@lem3644332 A B t s f u)). Qed.
Lemma lem3644335 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : ((term466 A B t s f u) = (term467 A B t s f u)) = ((term463 A B t s f u) = (term480 A B t s f u)).
Proof. exact (MK_COMB (@lem3644326 A B t s f u) (@lem3644334 A B t s f u)). Qed.
Lemma lem3644336 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term463 A B t s f u) = (term480 A B t s f u).
Proof. exact (EQ_MP (@lem3644335 A B t s f u) (@lem3644316 A B t s f u)). Qed.
Lemma lem3644338 {A : Type'} (P : Prop) (Q : A -> Prop) : (term287 A P Q) = (term288 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3644339 {B : Type'} (P : Prop) (Q : B -> Prop) : (term287 B P Q) = (term288 B P Q).
Proof. exact (@lem3644338 B P Q). Qed.
Lemma lem3644340 {A B : Type'} (t : A -> Prop) (x : A) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term481 A B t x s f u) = (term482 A B t x s f u).
Proof. exact (@lem3644339 B (term372 A u t x) (term461 A B s f u)). Qed.
Lemma lem3644341 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term483 A B s f u x) = (term460 A B s x f u).
Proof. exact (eq_refl (term483 A B s f u x)). Qed.
Lemma lem3644342 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term484 A B s f u) = (term461 A B s f u).
Proof. exact (fun_ext (fun x : B => @lem3644341 A B s x f u)). Qed.
Lemma lem3644343 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3644344 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term485 A B s f u) = (term462 A B s f u).
Proof. exact (MK_COMB (@lem3644343 B) (@lem3644342 A B s f u)). Qed.
Lemma lem3644345 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) : (term475 A u t x) = (term475 A u t x).
Proof. exact (eq_refl (term475 A u t x)). Qed.
Lemma lem3644346 {A B : Type'} (t : A -> Prop) (x : A) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term481 A B t x s f u) = (term477 A B t x s f u).
Proof. exact (MK_COMB (@lem3644345 A u t x) (@lem3644344 A B s f u)). Qed.
Lemma lem3644347 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3644348 {A B : Type'} (t : A -> Prop) (x : A) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term486 A B t x s f u) = (term487 A B t x s f u).
Proof. exact (MK_COMB (@lem3644347) (@lem3644346 A B t x s f u)). Qed.
Lemma lem3644349 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term483 A B s f u x) = (term460 A B s x f u).
Proof. exact (eq_refl (term483 A B s f u x)). Qed.
Lemma lem3644350 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) : (term475 A u t x) = (term475 A u t x).
Proof. exact (eq_refl (term475 A u t x)). Qed.
Lemma lem3644351 {A B : Type'} (t : A -> Prop) (x : A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) : (term488 A B t x s f u x') = (term489 A B t x s x' f u).
Proof. exact (MK_COMB (@lem3644350 A u t x) (@lem3644349 A B s x' f u)). Qed.
Lemma lem3644352 {A B : Type'} (t : A -> Prop) (x : A) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term490 A B t x s f u) = (term491 A B t x s f u).
Proof. exact (fun_ext (fun x' : B => @lem3644351 A B t x s x' f u)). Qed.
Lemma lem3644353 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3644354 {A B : Type'} (t : A -> Prop) (x : A) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term482 A B t x s f u) = (term492 A B t x s f u).
Proof. exact (MK_COMB (@lem3644353 B) (@lem3644352 A B t x s f u)). Qed.
Lemma lem3644355 {A B : Type'} (t : A -> Prop) (x : A) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : ((term481 A B t x s f u) = (term482 A B t x s f u)) = ((term477 A B t x s f u) = (term492 A B t x s f u)).
Proof. exact (MK_COMB (@lem3644348 A B t x s f u) (@lem3644354 A B t x s f u)). Qed.
Lemma lem3644356 {A B : Type'} (t : A -> Prop) (x : A) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term477 A B t x s f u) = (term492 A B t x s f u).
Proof. exact (EQ_MP (@lem3644355 A B t x s f u) (@lem3644340 A B t x s f u)). Qed.
Lemma lem3644358 {A : Type'} (P : Prop) (Q : A -> Prop) : (term287 A P Q) = (term288 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3644359 {A : Type'} (P : Prop) (Q : A -> Prop) : (term287 A P Q) = (term288 A P Q).
Proof. exact (@lem3644358 A P Q). Qed.
Lemma lem3644360 {A B : Type'} (t : A -> Prop) (x : A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) : (term493 A B t x s x' f u) = (term494 A B t x s x' f u).
Proof. exact (@lem3644359 A (term372 A u t x) (term459 A B s x' f u)). Qed.
Lemma lem3644361 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term495 A B s x f u x') = (term457 A B s x f u x').
Proof. exact (eq_refl (term495 A B s x f u x')). Qed.
Lemma lem3644362 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term496 A B s x f u) = (term459 A B s x f u).
Proof. exact (fun_ext (fun x' : A => @lem3644361 A B s x f u x')). Qed.
Lemma lem3644363 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3644364 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term497 A B s x f u) = (term460 A B s x f u).
Proof. exact (MK_COMB (@lem3644363 A) (@lem3644362 A B s x f u)). Qed.
Lemma lem3644365 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) : (term475 A u t x) = (term475 A u t x).
Proof. exact (eq_refl (term475 A u t x)). Qed.
Lemma lem3644366 {A B : Type'} (t : A -> Prop) (x : A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) : (term493 A B t x s x' f u) = (term489 A B t x s x' f u).
Proof. exact (MK_COMB (@lem3644365 A u t x) (@lem3644364 A B s x' f u)). Qed.
Lemma lem3644367 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3644368 {A B : Type'} (t : A -> Prop) (x : A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) : (term498 A B t x s x' f u) = (term499 A B t x s x' f u).
Proof. exact (MK_COMB (@lem3644367) (@lem3644366 A B t x s x' f u)). Qed.
Lemma lem3644369 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term495 A B s x f u x') = (term457 A B s x f u x').
Proof. exact (eq_refl (term495 A B s x f u x')). Qed.
Lemma lem3644370 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) : (term475 A u t x) = (term475 A u t x).
Proof. exact (eq_refl (term475 A u t x)). Qed.
Lemma lem3644371 {A B : Type'} (t : A -> Prop) (x : A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (x'' : A) : (term500 A B t x s x' f u x'') = (term501 A B t x s x' f u x'').
Proof. exact (MK_COMB (@lem3644370 A u t x) (@lem3644369 A B s x' f u x'')). Qed.
Lemma lem3644372 {A B : Type'} (t : A -> Prop) (x : A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) : (term502 A B t x s x' f u) = (term503 A B t x s x' f u).
Proof. exact (fun_ext (fun x'' : A => @lem3644371 A B t x s x' f u x'')). Qed.
Lemma lem3644373 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3644374 {A B : Type'} (t : A -> Prop) (x : A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) : (term494 A B t x s x' f u) = (term504 A B t x s x' f u).
Proof. exact (MK_COMB (@lem3644373 A) (@lem3644372 A B t x s x' f u)). Qed.
Lemma lem3644375 {A B : Type'} (t : A -> Prop) (x : A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) : ((term493 A B t x s x' f u) = (term494 A B t x s x' f u)) = ((term489 A B t x s x' f u) = (term504 A B t x s x' f u)).
Proof. exact (MK_COMB (@lem3644368 A B t x s x' f u) (@lem3644374 A B t x s x' f u)). Qed.
Lemma lem3644376 {A B : Type'} (t : A -> Prop) (x : A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) : (term489 A B t x s x' f u) = (term504 A B t x s x' f u).
Proof. exact (EQ_MP (@lem3644375 A B t x s x' f u) (@lem3644360 A B t x s x' f u)). Qed.
Lemma lem3644377 {A B : Type'} (t : A -> Prop) (x : A) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term491 A B t x s f u) = (term505 A B t x s f u).
Proof. exact (fun_ext (fun x' : B => @lem3644376 A B t x s x' f u)). Qed.
Lemma lem3644378 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3644379 {A B : Type'} (t : A -> Prop) (x : A) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term492 A B t x s f u) = (term506 A B t x s f u).
Proof. exact (MK_COMB (@lem3644378 B) (@lem3644377 A B t x s f u)). Qed.
Lemma lem3644380 {A B : Type'} (t : A -> Prop) (x : A) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term477 A B t x s f u) = (term506 A B t x s f u).
Proof. exact (TRANS (@lem3644356 A B t x s f u) (@lem3644379 A B t x s f u)). Qed.
Lemma lem3644381 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term479 A B t s f u) = (term507 A B t s f u).
Proof. exact (fun_ext (fun x : A => @lem3644380 A B t x s f u)). Qed.
Lemma lem3644382 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3644383 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term480 A B t s f u) = (term508 A B t s f u).
Proof. exact (MK_COMB (@lem3644382 A) (@lem3644381 A B t s f u)). Qed.
Lemma lem3644384 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term463 A B t s f u) = (term508 A B t s f u).
Proof. exact (TRANS (@lem3644336 A B t s f u) (@lem3644383 A B t s f u)). Qed.
Lemma lem3644385 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term424 A B t s f u) = (term508 A B t s f u).
Proof. exact (TRANS (@lem3644310 A B t s f u) (@lem3644384 A B t s f u)). Qed.
Lemma lem3644386 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term401 A B t s f u) = (term508 A B t s f u).
Proof. exact (TRANS (@lem3644231 A B t s f u) (@lem3644385 A B t s f u)). Qed.
Lemma lem3644387 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term222 A B t s f u) = (term508 A B t s f u).
Proof. exact (TRANS (@lem3644018 A B t s f u) (@lem3644386 A B t s f u)). Qed.
Lemma lem3644388 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (h1 : term222 A B t s f u) : term508 A B t s f u.
Proof. exact (EQ_MP (@lem3644387 A B t s f u) (@lem3643461 A B t s f u h1)). Qed.
Lemma lem3644389 {A B : Type'} (t : A -> Prop) (x : A) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (h1 : term506 A B t x s f u) : term506 A B t x s f u.
Proof. exact (h1). Qed.
Lemma lem3644390 {A B : Type'} (t : A -> Prop) (x : A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (h1 : term504 A B t x s x' f u) : term504 A B t x s x' f u.
Proof. exact (h1). Qed.
Lemma lem3644391 {A B : Type'} (t : A -> Prop) (x : A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (x'' : A) (h1 : term501 A B t x s x' f u x'') : term501 A B t x s x' f u x''.
Proof. exact (h1). Qed.
Lemma lem3644392 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term367 A B t s f u x'''.
Proof. exact (h1). Qed.
Lemma lem3644413 {A B : Type'} (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (x'' : A) : (term430 A B s x' f u x'') = (term430 A B s x' f u x'').
Proof. exact (eq_refl (term430 A B s x' f u x'')). Qed.
Lemma lem3644430 {A B : Type'} (x' : B) (f : A -> B) (u : A -> Prop) (x : A) : (term238 A B x' f u x) = (term238 A B x' f u x).
Proof. exact (eq_refl (term238 A B x' f u x)). Qed.
Lemma lem3644431 {A B : Type'} (x' : B) (f : A -> B) (u : A -> Prop) : (term246 A B x' f u) = (term246 A B x' f u).
Proof. exact (fun_ext (fun x : A => @lem3644430 A B x' f u x)). Qed.
Lemma lem3644432 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3644433 {A B : Type'} (x' : B) (f : A -> B) (u : A -> Prop) : (term247 A B x' f u) = (term247 A B x' f u).
Proof. exact (MK_COMB (@lem3644432 A) (@lem3644431 A B x' f u)). Qed.
Lemma lem3644438 {B : Type'} (s : B -> Prop) (x' : B) : (term167 B s x') = (term167 B s x').
Proof. exact (eq_refl (term167 B s x')). Qed.
Lemma lem3644439 {A B : Type'} (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) : (term385 A B s x' f u) = (term385 A B s x' f u).
Proof. exact (MK_COMB (@lem3644438 B s x') (@lem3644433 A B x' f u)). Qed.
Lemma lem3644440 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3644441 {A B : Type'} (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) : (term387 A B s x' f u) = (term387 A B s x' f u).
Proof. exact (MK_COMB (@lem3644440) (@lem3644439 A B s x' f u)). Qed.
Lemma lem3644442 {A B : Type'} (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (x'' : A) : (term457 A B s x' f u x'') = (term457 A B s x' f u x'').
Proof. exact (MK_COMB (@lem3644441 A B s x' f u) (@lem3644413 A B s x' f u x'')). Qed.
Lemma lem3644455 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) : (term475 A u t x) = (term475 A u t x).
Proof. exact (eq_refl (term475 A u t x)). Qed.
Lemma lem3644456 {A B : Type'} (t : A -> Prop) (x : A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (x'' : A) : (term501 A B t x s x' f u x'') = (term501 A B t x s x' f u x'').
Proof. exact (MK_COMB (@lem3644455 A u t x) (@lem3644442 A B s x' f u x'')). Qed.
Lemma lem3644457 {A B : Type'} (t : A -> Prop) (x : A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (x'' : A) (h1 : term501 A B t x s x' f u x'') : term501 A B t x s x' f u x''.
Proof. exact (EQ_MP (@lem3644456 A B t x s x' f u x'') (@lem3644391 A B t x s x' f u x'' h1)). Qed.
Lemma lem3644482 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (x : B) : (term320 A B s f u x''' x) = (term320 A B s f u x''' x).
Proof. exact (eq_refl (term320 A B s f u x''' x)). Qed.
Lemma lem3644483 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) : (term322 A B s f u x''') = (term322 A B s f u x''').
Proof. exact (fun_ext (fun x : B => @lem3644482 A B s f u x''' x)). Qed.
Lemma lem3644484 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3644485 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) : (term324 A B s f u x''') = (term324 A B s f u x''').
Proof. exact (MK_COMB (@lem3644484 B) (@lem3644483 A B s f u x''')). Qed.
Lemma lem3644502 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term238 A B x f u x') = (term238 A B x f u x').
Proof. exact (eq_refl (term238 A B x f u x')). Qed.
Lemma lem3644503 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) : (term246 A B x f u) = (term246 A B x f u).
Proof. exact (fun_ext (fun x' : A => @lem3644502 A B x f u x')). Qed.
Lemma lem3644504 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3644505 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) : (term247 A B x f u) = (term247 A B x f u).
Proof. exact (MK_COMB (@lem3644504 A) (@lem3644503 A B x f u)). Qed.
Lemma lem3644510 {B : Type'} (s : B -> Prop) (x : B) : (term250 B s x) = (term250 B s x).
Proof. exact (eq_refl (term250 B s x)). Qed.
Lemma lem3644511 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term252 A B s x f u) = (term252 A B s x f u).
Proof. exact (MK_COMB (@lem3644510 B s x) (@lem3644505 A B x f u)). Qed.
Lemma lem3644512 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term267 A B s f u) = (term267 A B s f u).
Proof. exact (fun_ext (fun x : B => @lem3644511 A B s x f u)). Qed.
Lemma lem3644513 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3644514 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term278 A B s f u) = (term278 A B s f u).
Proof. exact (MK_COMB (@lem3644513 B) (@lem3644512 A B s f u)). Qed.
Lemma lem3644515 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3644516 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term280 A B s f u) = (term280 A B s f u).
Proof. exact (MK_COMB (@lem3644515) (@lem3644514 A B s f u)). Qed.
Lemma lem3644517 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) : (term341 A B s f u x''') = (term341 A B s f u x''').
Proof. exact (MK_COMB (@lem3644516 A B s f u) (@lem3644485 A B s f u x''')). Qed.
Lemma lem3644574 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : A) : (term232 A B u f x y) = (term232 A B u f x y).
Proof. exact (eq_refl (term232 A B u f x y)). Qed.
Lemma lem3644575 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) : (term233 A B u f x) = (term233 A B u f x).
Proof. exact (fun_ext (fun y : A => @lem3644574 A B u f x y)). Qed.
Lemma lem3644576 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3644577 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) : (term234 A B u f x) = (term234 A B u f x).
Proof. exact (MK_COMB (@lem3644576 A) (@lem3644575 A B u f x)). Qed.
Lemma lem3644578 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term235 A B u f) = (term235 A B u f).
Proof. exact (fun_ext (fun x : A => @lem3644577 A B u f x)). Qed.
Lemma lem3644579 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3644580 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term236 A B u f) = (term236 A B u f).
Proof. exact (MK_COMB (@lem3644579 A) (@lem3644578 A B u f)). Qed.
Lemma lem3644581 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3644582 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term259 A B u f) = (term259 A B u f).
Proof. exact (MK_COMB (@lem3644581) (@lem3644580 A B u f)). Qed.
Lemma lem3644583 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) : (term354 A B s f u x''') = (term354 A B s f u x''').
Proof. exact (MK_COMB (@lem3644582 A B u f) (@lem3644517 A B s f u x''')). Qed.
Lemma lem3644594 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) : (term223 A u t x) = (term223 A u t x).
Proof. exact (eq_refl (term223 A u t x)). Qed.
Lemma lem3644595 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term224 A u t) = (term224 A u t).
Proof. exact (fun_ext (fun x : A => @lem3644594 A u t x)). Qed.
Lemma lem3644596 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3644597 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term225 A u t) = (term225 A u t).
Proof. exact (MK_COMB (@lem3644596 A) (@lem3644595 A u t)). Qed.
Lemma lem3644598 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3644599 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term261 A u t) = (term261 A u t).
Proof. exact (MK_COMB (@lem3644598) (@lem3644597 A u t)). Qed.
Lemma lem3644600 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) : (term367 A B t s f u x''') = (term367 A B t s f u x''').
Proof. exact (MK_COMB (@lem3644599 A u t) (@lem3644583 A B s f u x''')). Qed.
Lemma lem3644601 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term367 A B t s f u x'''.
Proof. exact (EQ_MP (@lem3644600 A B t s f u x''') (@lem3644392 A B t s f u x''' h1)). Qed.
Lemma lem3644602 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term354 A B s f u x'''.
Proof. exact (proj2 (@lem3644601 A B t s f u x''' h1)). Qed.
Lemma lem3644603 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term225 A u t.
Proof. exact (proj1 (@lem3644601 A B t s f u x''' h1)). Qed.
Lemma lem3644604 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term341 A B s f u x'''.
Proof. exact (proj2 (@lem3644602 A B t s f u x''' h1)). Qed.
Lemma lem3644606 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term324 A B s f u x'''.
Proof. exact (proj2 (@lem3644604 A B t s f u x''' h1)). Qed.
Lemma lem3644607 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term278 A B s f u.
Proof. exact (proj1 (@lem3644604 A B t s f u x''' h1)). Qed.
Lemma lem3644608 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) (h1 : term372 A u t x) : term372 A u t x.
Proof. exact (h1). Qed.
Lemma lem3644609 {A B : Type'} (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (x'' : A) (h1 : term457 A B s x' f u x'') : term457 A B s x' f u x''.
Proof. exact (h1). Qed.
Lemma lem3644612 {A B : Type'} (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (h1 : term385 A B s x' f u) : term385 A B s x' f u.
Proof. exact (h1). Qed.
Lemma lem3644613 {A B : Type'} (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (x'' : A) (h1 : term430 A B s x' f u x'') : term430 A B s x' f u x''.
Proof. exact (h1). Qed.
Lemma lem3644614 {A B : Type'} (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (h1 : term385 A B s x' f u) : term247 A B x' f u.
Proof. exact (proj2 (@lem3644612 A B s x' f u h1)). Qed.
Lemma lem3644616 {A B : Type'} (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (x'' : A) (h1 : term430 A B s x' f u x'') : term189 A B x' f u x''.
Proof. exact (proj2 (@lem3644613 A B s x' f u x'' h1)). Qed.
Lemma lem3644627 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) : (term223 A u t x) = (term223 A u t x).
Proof. exact (eq_refl (term223 A u t x)). Qed.
Lemma lem3644628 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term224 A u t) = (term224 A u t).
Proof. exact (fun_ext (fun x : A => @lem3644627 A u t x)). Qed.
Lemma lem3644629 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3644631 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term225 A u t) = (term225 A u t).
Proof. exact (MK_COMB (@lem3644629 A) (@lem3644628 A u t)). Qed.
Lemma lem3644632 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term225 A u t.
Proof. exact (EQ_MP (@lem3644631 A u t) (@lem3644603 A B t s f u x''' h1)). Qed.
Lemma lem3644870 {A B : Type'} (f : A -> B) (s : B -> Prop) (u : A -> Prop) (x''' : B -> A) (x : B) : (term320 A B s f u x''' x) = (term509 A B f s u x''' x).
Proof. exact (@lem19490 (x = (term510 A B f x''' x)) (term291 B s x) (term511 A B u x''' x)). Qed.
Lemma lem3644871 {A B : Type'} (f : A -> B) (s : B -> Prop) (u : A -> Prop) (x''' : B -> A) : (term322 A B s f u x''') = (term512 A B f s u x''').
Proof. exact (fun_ext (fun x : B => @lem3644870 A B f s u x''' x)). Qed.
Lemma lem3644872 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3644874 {A B : Type'} (f : A -> B) (s : B -> Prop) (u : A -> Prop) (x''' : B -> A) : (term324 A B s f u x''') = (term513 A B f s u x''').
Proof. exact (MK_COMB (@lem3644872 B) (@lem3644871 A B f s u x''')). Qed.
Lemma lem3644875 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term513 A B f s u x'''.
Proof. exact (EQ_MP (@lem3644874 A B f s u x''') (@lem3644606 A B t s f u x''' h1)). Qed.
Lemma lem3644887 {A B : Type'} (x' : B) (f : A -> B) (u : A -> Prop) (x : A) : (term238 A B x' f u x) = (term238 A B x' f u x).
Proof. exact (eq_refl (term238 A B x' f u x)). Qed.
Lemma lem3644888 {A B : Type'} (x' : B) (f : A -> B) (u : A -> Prop) : (term246 A B x' f u) = (term246 A B x' f u).
Proof. exact (fun_ext (fun x : A => @lem3644887 A B x' f u x)). Qed.
Lemma lem3644889 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3644891 {A B : Type'} (x' : B) (f : A -> B) (u : A -> Prop) : (term247 A B x' f u) = (term247 A B x' f u).
Proof. exact (MK_COMB (@lem3644889 A) (@lem3644888 A B x' f u)). Qed.
Lemma lem3644892 {A B : Type'} (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (h1 : term385 A B s x' f u) : term247 A B x' f u.
Proof. exact (EQ_MP (@lem3644891 A B x' f u) (@lem3644614 A B s x' f u h1)). Qed.
Lemma lem3644951 {A : Type'} (P : Prop) (Q : A -> Prop) : (term514 A P Q) = (term515 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3644952 {A : Type'} (P : Prop) (Q : A -> Prop) : (term514 A P Q) = (term515 A P Q).
Proof. exact (@lem3644951 A P Q). Qed.
Lemma lem3644953 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term516 A B s x f u) = (term517 A B s x f u).
Proof. exact (@lem3644952 A (s x) (term246 A B x f u)). Qed.
Lemma lem3644954 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term518 A B x f u x') = (term238 A B x f u x').
Proof. exact (eq_refl (term518 A B x f u x')). Qed.
Lemma lem3644955 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) : (term519 A B x f u) = (term246 A B x f u).
Proof. exact (fun_ext (fun x' : A => @lem3644954 A B x f u x')). Qed.
Lemma lem3644956 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3644957 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) : (term520 A B x f u) = (term247 A B x f u).
Proof. exact (MK_COMB (@lem3644956 A) (@lem3644955 A B x f u)). Qed.
Lemma lem3644958 {B : Type'} (s : B -> Prop) (x : B) : (term250 B s x) = (term250 B s x).
Proof. exact (eq_refl (term250 B s x)). Qed.
Lemma lem3644959 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term516 A B s x f u) = (term252 A B s x f u).
Proof. exact (MK_COMB (@lem3644958 B s x) (@lem3644957 A B x f u)). Qed.
Lemma lem3644960 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3644961 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term521 A B s x f u) = (term522 A B s x f u).
Proof. exact (MK_COMB (@lem3644960) (@lem3644959 A B s x f u)). Qed.
Lemma lem3644962 {A B : Type'} (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term518 A B x f u x') = (term238 A B x f u x').
Proof. exact (eq_refl (term518 A B x f u x')). Qed.
Lemma lem3644963 {B : Type'} (s : B -> Prop) (x : B) : (term250 B s x) = (term250 B s x).
Proof. exact (eq_refl (term250 B s x)). Qed.
Lemma lem3644964 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term523 A B s x f u x') = (term524 A B s x f u x').
Proof. exact (MK_COMB (@lem3644963 B s x) (@lem3644962 A B x f u x')). Qed.
Lemma lem3644965 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term525 A B s x f u) = (term526 A B s x f u).
Proof. exact (fun_ext (fun x' : A => @lem3644964 A B s x f u x')). Qed.
Lemma lem3644966 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3644967 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term517 A B s x f u) = (term527 A B s x f u).
Proof. exact (MK_COMB (@lem3644966 A) (@lem3644965 A B s x f u)). Qed.
Lemma lem3644968 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : ((term516 A B s x f u) = (term517 A B s x f u)) = ((term252 A B s x f u) = (term527 A B s x f u)).
Proof. exact (MK_COMB (@lem3644961 A B s x f u) (@lem3644967 A B s x f u)). Qed.
Lemma lem3644969 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term252 A B s x f u) = (term527 A B s x f u).
Proof. exact (EQ_MP (@lem3644968 A B s x f u) (@lem3644953 A B s x f u)). Qed.
Lemma lem3644970 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term267 A B s f u) = (term528 A B s f u).
Proof. exact (fun_ext (fun x : B => @lem3644969 A B s x f u)). Qed.
Lemma lem3644971 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3644972 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term278 A B s f u) = (term529 A B s f u).
Proof. exact (MK_COMB (@lem3644971 B) (@lem3644970 A B s f u)). Qed.
Lemma lem3644985 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) (x' : A) : (term524 A B s x f u x') = (term524 A B s x f u x').
Proof. exact (eq_refl (term524 A B s x f u x')). Qed.
Lemma lem3644986 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term526 A B s x f u) = (term526 A B s x f u).
Proof. exact (fun_ext (fun x' : A => @lem3644985 A B s x f u x')). Qed.
Lemma lem3644987 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3644988 {A B : Type'} (s : B -> Prop) (x : B) (f : A -> B) (u : A -> Prop) : (term527 A B s x f u) = (term527 A B s x f u).
Proof. exact (MK_COMB (@lem3644987 A) (@lem3644986 A B s x f u)). Qed.
Lemma lem3644989 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term528 A B s f u) = (term528 A B s f u).
Proof. exact (fun_ext (fun x : B => @lem3644988 A B s x f u)). Qed.
Lemma lem3644990 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3644991 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term529 A B s f u) = (term529 A B s f u).
Proof. exact (MK_COMB (@lem3644990 B) (@lem3644989 A B s f u)). Qed.
Lemma lem3644992 {A B : Type'} (s : B -> Prop) (f : A -> B) (u : A -> Prop) : (term278 A B s f u) = (term529 A B s f u).
Proof. exact (TRANS (@lem3644972 A B s f u) (@lem3644991 A B s f u)). Qed.
Lemma lem3644993 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term529 A B s f u.
Proof. exact (EQ_MP (@lem3644992 A B s f u) (@lem3644607 A B t s f u x''' h1)). Qed.
Lemma lem3645029 {A B : Type'} (_39938 : A) (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term530 A u t _39938.
Proof. exact (@lem3644632 A B t s f u x''' h1 _39938). Qed.
Lemma lem3645030 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_39938 : A) : (term530 A u t _39938) = (term223 A u t _39938).
Proof. exact (eq_refl (term530 A u t _39938)). Qed.
Lemma lem3645062 {A B : Type'} (_39949 : B) (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term531 A B f s u x''' _39949.
Proof. exact (@lem3644875 A B t s f u x''' h1 _39949). Qed.
Lemma lem3645063 {A B : Type'} (f : A -> B) (s : B -> Prop) (u : A -> Prop) (x''' : B -> A) (_39949 : B) : (term531 A B f s u x''' _39949) = (term509 A B f s u x''' _39949).
Proof. exact (eq_refl (term531 A B f s u x''' _39949)). Qed.
Lemma lem3645064 {A B : Type'} (_39949 : B) (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term509 A B f s u x''' _39949.
Proof. exact (EQ_MP (@lem3645063 A B f s u x''' _39949) (@lem3645062 A B _39949 t s f u x''' h1)). Qed.
Lemma lem3645065 {A B : Type'} (_39950 : A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (h1 : term385 A B s x' f u) : term518 A B x' f u _39950.
Proof. exact (@lem3644892 A B s x' f u h1 _39950). Qed.
Lemma lem3645066 {A B : Type'} (x' : B) (f : A -> B) (u : A -> Prop) (_39950 : A) : (term518 A B x' f u _39950) = (term238 A B x' f u _39950).
Proof. exact (eq_refl (term518 A B x' f u _39950)). Qed.
Lemma lem3645077 {A B : Type'} (_39954 : B) (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term532 A B s f u _39954.
Proof. exact (@lem3644993 A B t s f u x''' h1 _39954). Qed.
Lemma lem3645078 {A B : Type'} (s : B -> Prop) (_39954 : B) (f : A -> B) (u : A -> Prop) : (term532 A B s f u _39954) = (term527 A B s _39954 f u).
Proof. exact (eq_refl (term532 A B s f u _39954)). Qed.
Lemma lem3645079 {A B : Type'} (_39954 : B) (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term527 A B s _39954 f u.
Proof. exact (EQ_MP (@lem3645078 A B s _39954 f u) (@lem3645077 A B _39954 t s f u x''' h1)). Qed.
Lemma lem3645080 {A B : Type'} (_39954 : B) (_39955 : A) (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term533 A B s _39954 f u _39955.
Proof. exact (@lem3645079 A B _39954 t s f u x''' h1 _39955). Qed.
Lemma lem3645081 {A B : Type'} (s : B -> Prop) (_39954 : B) (f : A -> B) (u : A -> Prop) (_39955 : A) : (term533 A B s _39954 f u _39955) = (term524 A B s _39954 f u _39955).
Proof. exact (eq_refl (term533 A B s _39954 f u _39955)). Qed.
Lemma lem3645103 {A B : Type'} (_39938 : A) (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term223 A u t _39938.
Proof. exact (EQ_MP (@lem3645030 A u t _39938) (@lem3645029 A B _39938 t s f u x''' h1)). Qed.
Lemma lem3645117 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) (h1 : term372 A u t x) : term291 A t x.
Proof. exact (proj2 (@lem3644608 A u t x h1)). Qed.
Lemma lem3645185 {A B : Type'} (_39950 : A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (h1 : term385 A B s x' f u) : term238 A B x' f u _39950.
Proof. exact (EQ_MP (@lem3645066 A B x' f u _39950) (@lem3645065 A B _39950 s x' f u h1)). Qed.
Lemma lem3645191 {A B : Type'} (_39949 : B) (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term534 A B s f x''' _39949.
Proof. exact (proj1 (@lem3645064 A B _39949 t s f u x''' h1)). Qed.
Lemma lem3645197 {A B : Type'} (_39949 : B) (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term535 A B s u x''' _39949.
Proof. exact (proj2 (@lem3645064 A B _39949 t s f u x''' h1)). Qed.
Lemma lem3645247 {A B : Type'} (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (x'' : A) (h1 : term430 A B s x' f u x'') : term291 B s x'.
Proof. exact (proj1 (@lem3644613 A B s x' f u x'' h1)). Qed.
Lemma lem3645249 {A B : Type'} (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (x'' : A) (h1 : term430 A B s x' f u x'') : x' = (f x'').
Proof. exact (proj1 (@lem3644616 A B s x' f u x'' h1)). Qed.
Lemma lem3645337 {A B : Type'} (_39954 : B) (_39955 : A) (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term524 A B s _39954 f u _39955.
Proof. exact (EQ_MP (@lem3645081 A B s _39954 f u _39955) (@lem3645080 A B _39954 _39955 t s f u x''' h1)). Qed.
Lemma lem3645338 {B : Type'} (s : B -> Prop) : (term536 B s) = (term536 B s).
Proof. exact (eq_refl (term536 B s)). Qed.
Lemma lem3645339 {A B : Type'} (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (x'' : A) (h1 : term430 A B s x' f u x'') : (term537 B s x') = (term538 A B s f x'').
Proof. exact (MK_COMB (@lem3645338 B s) (@lem3645249 A B s x' f u x'' h1)). Qed.
Lemma lem3645340 {A B : Type'} (s : B -> Prop) (f : A -> B) (x'' : A) : (term538 A B s f x'') = (term539 A B s f x'').
Proof. exact (eq_refl (term538 A B s f x'')). Qed.
Lemma lem3645341 {B : Type'} (s : B -> Prop) (x' : B) : (term540 B s x') = (term540 B s x').
Proof. exact (eq_refl (term540 B s x')). Qed.
Lemma lem3645342 {A B : Type'} (x' : B) (s : B -> Prop) (f : A -> B) (x'' : A) : ((term537 B s x') = (term538 A B s f x'')) = ((term537 B s x') = (term539 A B s f x'')).
Proof. exact (MK_COMB (@lem3645341 B s x') (@lem3645340 A B s f x'')). Qed.
Lemma lem3645343 {B : Type'} (s : B -> Prop) (x' : B) : (term537 B s x') = (term291 B s x').
Proof. exact (eq_refl (term537 B s x')). Qed.
Lemma lem3645344 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3645345 {B : Type'} (s : B -> Prop) (x' : B) : (term540 B s x') = (term541 B s x').
Proof. exact (MK_COMB (@lem3645344) (@lem3645343 B s x')). Qed.
Lemma lem3645346 {A B : Type'} (s : B -> Prop) (f : A -> B) (x'' : A) : (term539 A B s f x'') = (term539 A B s f x'').
Proof. exact (eq_refl (term539 A B s f x'')). Qed.
Lemma lem3645347 {A B : Type'} (x' : B) (s : B -> Prop) (f : A -> B) (x'' : A) : ((term537 B s x') = (term539 A B s f x'')) = ((term291 B s x') = (term539 A B s f x'')).
Proof. exact (MK_COMB (@lem3645345 B s x') (@lem3645346 A B s f x'')). Qed.
Lemma lem3645348 {A B : Type'} (x' : B) (s : B -> Prop) (f : A -> B) (x'' : A) : ((term537 B s x') = (term538 A B s f x'')) = ((term291 B s x') = (term539 A B s f x'')).
Proof. exact (TRANS (@lem3645342 A B x' s f x'') (@lem3645347 A B x' s f x'')). Qed.
Lemma lem3645349 {A B : Type'} (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (x'' : A) (h1 : term430 A B s x' f u x'') : (term291 B s x') = (term539 A B s f x'').
Proof. exact (EQ_MP (@lem3645348 A B x' s f x'') (@lem3645339 A B s x' f u x'' h1)). Qed.
Lemma lem3645350 {A B : Type'} (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (x'' : A) (h1 : term430 A B s x' f u x'') : term539 A B s f x''.
Proof. exact (EQ_MP (@lem3645349 A B s x' f u x'' h1) (@lem3645247 A B s x' f u x'' h1)). Qed.
Lemma lem3645478 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) (h1 : term372 A u t x) : u x.
Proof. exact (proj1 (@lem3644608 A u t x h1)). Qed.
Lemma lem3645479 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) (h1 : term372 A u t x) : term542 A u x.
Proof. exact (fun h0 : term291 A u x => @lem3645478 A u t x h1). Qed.
Lemma lem3645481 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3645482 {A : Type'} (u : A -> Prop) (x : A) : (term542 A u x) = (u x).
Proof. exact (@lem3645481 (u x)). Qed.
Lemma lem3645483 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) (h1 : term372 A u t x) : u x.
Proof. exact (EQ_MP (@lem3645482 A u x) (@lem3645479 A u t x h1)). Qed.
Lemma lem3645489 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3645490 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_39938 : A) : (term223 A u t _39938) = (term543 A t u _39938).
Proof. exact (@lem3645489 (t _39938) (term291 A u _39938)). Qed.
Lemma lem3645496 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3645497 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_39938 : A) : (term544 A u t _39938) = (term545 A t u _39938).
Proof. exact (MK_COMB (@lem3645496) (@lem3645490 A t u _39938)). Qed.
Lemma lem3645503 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_39938 : A) : (term543 A t u _39938) = (term543 A t u _39938).
Proof. exact (eq_refl (term543 A t u _39938)). Qed.
Lemma lem3645504 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_39938 : A) : ((term223 A u t _39938) = (term543 A t u _39938)) = ((term543 A t u _39938) = (term543 A t u _39938)).
Proof. exact (MK_COMB (@lem3645497 A t u _39938) (@lem3645503 A t u _39938)). Qed.
Lemma lem3645506 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3645507 (x : Prop) : (x = x) = True.
Proof. exact (@lem3645506 Prop x). Qed.
Lemma lem3645508 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_39938 : A) : ((term543 A t u _39938) = (term543 A t u _39938)) = True.
Proof. exact (@lem3645507 (term543 A t u _39938)). Qed.
Lemma lem3645509 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_39938 : A) : ((term223 A u t _39938) = (term543 A t u _39938)) = True.
Proof. exact (TRANS (@lem3645504 A t u _39938) (@lem3645508 A t u _39938)). Qed.
Lemma lem3645510 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_39938 : A) : True = ((term223 A u t _39938) = (term543 A t u _39938)).
Proof. exact (SYM (@lem3645509 A t u _39938)). Qed.
Lemma lem3645511 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_39938 : A) : (term223 A u t _39938) = (term543 A t u _39938).
Proof. exact (EQ_MP (@lem3645510 A t u _39938) (@lem0)). Qed.
Lemma lem3645512 {A B : Type'} (_39938 : A) (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term543 A t u _39938.
Proof. exact (EQ_MP (@lem3645511 A t u _39938) (@lem3645103 A B _39938 t s f u x''' h1)). Qed.
Lemma lem3645514 (b : Prop) (a : Prop) : (a \/ b) = (term109 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3645515 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_39938 : A) : (term543 A t u _39938) = (term546 A u t _39938).
Proof. exact (@lem3645514 (term291 A u _39938) (t _39938)). Qed.
Lemma lem3645517 (a : Prop) : (term111 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3645518 {A : Type'} (u : A -> Prop) (_39938 : A) : (term547 A u _39938) = (u _39938).
Proof. exact (@lem3645517 (u _39938)). Qed.
Lemma lem3645519 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3645520 {A : Type'} (u : A -> Prop) (_39938 : A) : (term548 A u _39938) = (term160 A u _39938).
Proof. exact (MK_COMB (@lem3645519) (@lem3645518 A u _39938)). Qed.
Lemma lem3645521 {A : Type'} (t : A -> Prop) (_39938 : A) : (t _39938) = (t _39938).
Proof. exact (eq_refl (t _39938)). Qed.
Lemma lem3645522 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_39938 : A) : (term546 A u t _39938) = (term162 A u t _39938).
Proof. exact (MK_COMB (@lem3645520 A u _39938) (@lem3645521 A t _39938)). Qed.
Lemma lem3645523 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_39938 : A) : (term543 A t u _39938) = (term162 A u t _39938).
Proof. exact (TRANS (@lem3645515 A u t _39938) (@lem3645522 A u t _39938)). Qed.
Lemma lem3645526 {A B : Type'} (_39938 : A) (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term162 A u t _39938.
Proof. exact (EQ_MP (@lem3645523 A u t _39938) (@lem3645512 A B _39938 t s f u x''' h1)). Qed.
Lemma lem3645527 {A B : Type'} (_39938 : A) (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term162 A u t _39938.
Proof. exact (@lem3645526 A B _39938 t s f u x''' h1). Qed.
Lemma lem3645528 {A B : Type'} (x : A) (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term162 A u t x.
Proof. exact (@lem3645527 A B x t s f u x''' h1). Qed.
Lemma lem3645531 {A B : Type'} (s : B -> Prop) (f : A -> B) (x''' : B -> A) (u : A -> Prop) (t : A -> Prop) (x : A) (h1 : term367 A B t s f u x''') (h2 : term372 A u t x) : t x.
Proof. exact (@lem3645528 A B x t s f u x''' h1 (@lem3645483 A u t x h2)). Qed.
Lemma lem3645532 {A B : Type'} (s : B -> Prop) (f : A -> B) (x''' : B -> A) (u : A -> Prop) (t : A -> Prop) (x : A) (h1 : term367 A B t s f u x''') (h2 : term372 A u t x) : term542 A t x.
Proof. exact (fun h0 : term291 A t x => @lem3645531 A B s f x''' u t x h1 h2). Qed.
Lemma lem3645534 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3645535 {A : Type'} (t : A -> Prop) (x : A) : (term542 A t x) = (t x).
Proof. exact (@lem3645534 (t x)). Qed.
Lemma lem3645536 {A B : Type'} (s : B -> Prop) (f : A -> B) (x''' : B -> A) (u : A -> Prop) (t : A -> Prop) (x : A) (h1 : term367 A B t s f u x''') (h2 : term372 A u t x) : t x.
Proof. exact (EQ_MP (@lem3645535 A t x) (@lem3645532 A B s f x''' u t x h1 h2)). Qed.
Lemma lem3645539 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3645541 {A : Type'} (t : A -> Prop) (x : A) : (term291 A t x) = (term549 A t x).
Proof. exact (@lem3645539 (t x)). Qed.
Lemma lem3645544 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) (h1 : term372 A u t x) : term549 A t x.
Proof. exact (EQ_MP (@lem3645541 A t x) (@lem3645117 A u t x h1)). Qed.
Lemma lem3645547 {A B : Type'} (s : B -> Prop) (f : A -> B) (x''' : B -> A) (u : A -> Prop) (t : A -> Prop) (x : A) (h1 : term367 A B t s f u x''') (h2 : term372 A u t x) : False.
Proof. exact (@lem3645544 A u t x h2 (@lem3645536 A B s f x''' u t x h1 h2)). Qed.
Lemma lem3645548 {A B : Type'} (s : B -> Prop) (f : A -> B) (x''' : B -> A) (u : A -> Prop) (t : A -> Prop) (x : A) (h1 : term367 A B t s f u x''') (h2 : term372 A u t x) : term117.
Proof. exact (fun h0 : ~ False => @lem3645547 A B s f x''' u t x h1 h2). Qed.
Lemma lem3645550 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3645551 : term117 = False.
Proof. exact (@lem3645550 False). Qed.
Lemma lem3645552 {A B : Type'} (s : B -> Prop) (f : A -> B) (x''' : B -> A) (u : A -> Prop) (t : A -> Prop) (x : A) (h1 : term367 A B t s f u x''') (h2 : term372 A u t x) : False.
Proof. exact (EQ_MP (@lem3645551) (@lem3645548 A B s f x''' u t x h1 h2)). Qed.
Lemma lem3645610 {A B : Type'} (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (h1 : term385 A B s x' f u) : s x'.
Proof. exact (proj1 (@lem3644612 A B s x' f u h1)). Qed.
Lemma lem3645611 {A B : Type'} (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (h1 : term385 A B s x' f u) : term542 B s x'.
Proof. exact (fun h0 : term291 B s x' => @lem3645610 A B s x' f u h1). Qed.
Lemma lem3645613 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3645614 {B : Type'} (s : B -> Prop) (x' : B) : (term542 B s x') = (s x').
Proof. exact (@lem3645613 (s x')). Qed.
Lemma lem3645615 {A B : Type'} (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (h1 : term385 A B s x' f u) : s x'.
Proof. exact (EQ_MP (@lem3645614 B s x') (@lem3645611 A B s x' f u h1)). Qed.
Lemma lem3645621 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3645622 {A B : Type'} (f : A -> B) (x''' : B -> A) (s : B -> Prop) (_39949 : B) : (term534 A B s f x''' _39949) = (term550 A B f x''' s _39949).
Proof. exact (@lem3645621 (_39949 = (term510 A B f x''' _39949)) (term291 B s _39949)). Qed.
Lemma lem3645630 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3645631 {A B : Type'} (f : A -> B) (x''' : B -> A) (s : B -> Prop) (_39949 : B) : (term551 A B s f x''' _39949) = (term552 A B f x''' s _39949).
Proof. exact (MK_COMB (@lem3645630) (@lem3645622 A B f x''' s _39949)). Qed.
Lemma lem3645639 {A B : Type'} (f : A -> B) (x''' : B -> A) (s : B -> Prop) (_39949 : B) : (term550 A B f x''' s _39949) = (term550 A B f x''' s _39949).
Proof. exact (eq_refl (term550 A B f x''' s _39949)). Qed.
Lemma lem3645640 {A B : Type'} (f : A -> B) (x''' : B -> A) (s : B -> Prop) (_39949 : B) : ((term534 A B s f x''' _39949) = (term550 A B f x''' s _39949)) = ((term550 A B f x''' s _39949) = (term550 A B f x''' s _39949)).
Proof. exact (MK_COMB (@lem3645631 A B f x''' s _39949) (@lem3645639 A B f x''' s _39949)). Qed.
Lemma lem3645642 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3645643 (x : Prop) : (x = x) = True.
Proof. exact (@lem3645642 Prop x). Qed.
Lemma lem3645644 {A B : Type'} (f : A -> B) (x''' : B -> A) (s : B -> Prop) (_39949 : B) : ((term550 A B f x''' s _39949) = (term550 A B f x''' s _39949)) = True.
Proof. exact (@lem3645643 (term550 A B f x''' s _39949)). Qed.
Lemma lem3645645 {A B : Type'} (f : A -> B) (x''' : B -> A) (s : B -> Prop) (_39949 : B) : ((term534 A B s f x''' _39949) = (term550 A B f x''' s _39949)) = True.
Proof. exact (TRANS (@lem3645640 A B f x''' s _39949) (@lem3645644 A B f x''' s _39949)). Qed.
Lemma lem3645646 {A B : Type'} (f : A -> B) (x''' : B -> A) (s : B -> Prop) (_39949 : B) : True = ((term534 A B s f x''' _39949) = (term550 A B f x''' s _39949)).
Proof. exact (SYM (@lem3645645 A B f x''' s _39949)). Qed.
Lemma lem3645647 {A B : Type'} (f : A -> B) (x''' : B -> A) (s : B -> Prop) (_39949 : B) : (term534 A B s f x''' _39949) = (term550 A B f x''' s _39949).
Proof. exact (EQ_MP (@lem3645646 A B f x''' s _39949) (@lem0)). Qed.
Lemma lem3645648 {A B : Type'} (_39949 : B) (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term550 A B f x''' s _39949.
Proof. exact (EQ_MP (@lem3645647 A B f x''' s _39949) (@lem3645191 A B _39949 t s f u x''' h1)). Qed.
Lemma lem3645650 (b : Prop) (a : Prop) : (a \/ b) = (term109 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3645651 {A B : Type'} (s : B -> Prop) (f : A -> B) (x''' : B -> A) (_39949 : B) : (term550 A B f x''' s _39949) = (term553 A B s f x''' _39949).
Proof. exact (@lem3645650 (term291 B s _39949) (_39949 = (term510 A B f x''' _39949))). Qed.
Lemma lem3645653 (a : Prop) : (term111 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3645654 {B : Type'} (s : B -> Prop) (_39949 : B) : (term547 B s _39949) = (s _39949).
Proof. exact (@lem3645653 (s _39949)). Qed.
Lemma lem3645655 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3645656 {B : Type'} (s : B -> Prop) (_39949 : B) : (term548 B s _39949) = (term160 B s _39949).
Proof. exact (MK_COMB (@lem3645655) (@lem3645654 B s _39949)). Qed.
Lemma lem3645657 {A B : Type'} (f : A -> B) (x''' : B -> A) (_39949 : B) : (_39949 = (term510 A B f x''' _39949)) = (_39949 = (term510 A B f x''' _39949)).
Proof. exact (eq_refl (_39949 = (term510 A B f x''' _39949))). Qed.
Lemma lem3645658 {A B : Type'} (s : B -> Prop) (f : A -> B) (x''' : B -> A) (_39949 : B) : (term553 A B s f x''' _39949) = (term554 A B s f x''' _39949).
Proof. exact (MK_COMB (@lem3645656 B s _39949) (@lem3645657 A B f x''' _39949)). Qed.
Lemma lem3645659 {A B : Type'} (s : B -> Prop) (f : A -> B) (x''' : B -> A) (_39949 : B) : (term550 A B f x''' s _39949) = (term554 A B s f x''' _39949).
Proof. exact (TRANS (@lem3645651 A B s f x''' _39949) (@lem3645658 A B s f x''' _39949)). Qed.
Lemma lem3645662 {A B : Type'} (_39949 : B) (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term554 A B s f x''' _39949.
Proof. exact (EQ_MP (@lem3645659 A B s f x''' _39949) (@lem3645648 A B _39949 t s f u x''' h1)). Qed.
Lemma lem3645663 {A B : Type'} (_39949 : B) (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term554 A B s f x''' _39949.
Proof. exact (@lem3645662 A B _39949 t s f u x''' h1). Qed.
Lemma lem3645664 {A B : Type'} (x' : B) (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term554 A B s f x''' x'.
Proof. exact (@lem3645663 A B x' t s f u x''' h1). Qed.
Lemma lem3645667 {A B : Type'} (t : A -> Prop) (x''' : B -> A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (h1 : term367 A B t s f u x''') (h2 : term385 A B s x' f u) : x' = (term510 A B f x''' x').
Proof. exact (@lem3645664 A B x' t s f u x''' h1 (@lem3645615 A B s x' f u h2)). Qed.
Lemma lem3645668 {A B : Type'} (t : A -> Prop) (x''' : B -> A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (h1 : term367 A B t s f u x''') (h2 : term385 A B s x' f u) : term555 A B f x''' x'.
Proof. exact (fun h0 : term556 A B f x''' x' => @lem3645667 A B t x''' s x' f u h1 h2). Qed.
Lemma lem3645670 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3645671 {A B : Type'} (f : A -> B) (x''' : B -> A) (x' : B) : (term555 A B f x''' x') = (x' = (term510 A B f x''' x')).
Proof. exact (@lem3645670 (x' = (term510 A B f x''' x'))). Qed.
Lemma lem3645672 {A B : Type'} (t : A -> Prop) (x''' : B -> A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (h1 : term367 A B t s f u x''') (h2 : term385 A B s x' f u) : x' = (term510 A B f x''' x').
Proof. exact (EQ_MP (@lem3645671 A B f x''' x') (@lem3645668 A B t x''' s x' f u h1 h2)). Qed.
Lemma lem3645674 {A B : Type'} (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (h1 : term385 A B s x' f u) : s x'.
Proof. exact (proj1 (@lem3644612 A B s x' f u h1)). Qed.
Lemma lem3645675 {A B : Type'} (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (h1 : term385 A B s x' f u) : term542 B s x'.
Proof. exact (fun h0 : term291 B s x' => @lem3645674 A B s x' f u h1). Qed.
Lemma lem3645677 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3645678 {B : Type'} (s : B -> Prop) (x' : B) : (term542 B s x') = (s x').
Proof. exact (@lem3645677 (s x')). Qed.
Lemma lem3645679 {A B : Type'} (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (h1 : term385 A B s x' f u) : s x'.
Proof. exact (EQ_MP (@lem3645678 B s x') (@lem3645675 A B s x' f u h1)). Qed.
Lemma lem3645685 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3645686 {A B : Type'} (u : A -> Prop) (x''' : B -> A) (s : B -> Prop) (_39949 : B) : (term535 A B s u x''' _39949) = (term557 A B u x''' s _39949).
Proof. exact (@lem3645685 (term511 A B u x''' _39949) (term291 B s _39949)). Qed.
Lemma lem3645692 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3645693 {A B : Type'} (u : A -> Prop) (x''' : B -> A) (s : B -> Prop) (_39949 : B) : (term558 A B s u x''' _39949) = (term559 A B u x''' s _39949).
Proof. exact (MK_COMB (@lem3645692) (@lem3645686 A B u x''' s _39949)). Qed.
Lemma lem3645699 {A B : Type'} (u : A -> Prop) (x''' : B -> A) (s : B -> Prop) (_39949 : B) : (term557 A B u x''' s _39949) = (term557 A B u x''' s _39949).
Proof. exact (eq_refl (term557 A B u x''' s _39949)). Qed.
Lemma lem3645700 {A B : Type'} (u : A -> Prop) (x''' : B -> A) (s : B -> Prop) (_39949 : B) : ((term535 A B s u x''' _39949) = (term557 A B u x''' s _39949)) = ((term557 A B u x''' s _39949) = (term557 A B u x''' s _39949)).
Proof. exact (MK_COMB (@lem3645693 A B u x''' s _39949) (@lem3645699 A B u x''' s _39949)). Qed.
Lemma lem3645702 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3645703 (x : Prop) : (x = x) = True.
Proof. exact (@lem3645702 Prop x). Qed.
Lemma lem3645704 {A B : Type'} (u : A -> Prop) (x''' : B -> A) (s : B -> Prop) (_39949 : B) : ((term557 A B u x''' s _39949) = (term557 A B u x''' s _39949)) = True.
Proof. exact (@lem3645703 (term557 A B u x''' s _39949)). Qed.
Lemma lem3645705 {A B : Type'} (u : A -> Prop) (x''' : B -> A) (s : B -> Prop) (_39949 : B) : ((term535 A B s u x''' _39949) = (term557 A B u x''' s _39949)) = True.
Proof. exact (TRANS (@lem3645700 A B u x''' s _39949) (@lem3645704 A B u x''' s _39949)). Qed.
Lemma lem3645706 {A B : Type'} (u : A -> Prop) (x''' : B -> A) (s : B -> Prop) (_39949 : B) : True = ((term535 A B s u x''' _39949) = (term557 A B u x''' s _39949)).
Proof. exact (SYM (@lem3645705 A B u x''' s _39949)). Qed.
Lemma lem3645707 {A B : Type'} (u : A -> Prop) (x''' : B -> A) (s : B -> Prop) (_39949 : B) : (term535 A B s u x''' _39949) = (term557 A B u x''' s _39949).
Proof. exact (EQ_MP (@lem3645706 A B u x''' s _39949) (@lem0)). Qed.
Lemma lem3645708 {A B : Type'} (_39949 : B) (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term557 A B u x''' s _39949.
Proof. exact (EQ_MP (@lem3645707 A B u x''' s _39949) (@lem3645197 A B _39949 t s f u x''' h1)). Qed.
Lemma lem3645710 (b : Prop) (a : Prop) : (a \/ b) = (term109 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3645711 {A B : Type'} (s : B -> Prop) (u : A -> Prop) (x''' : B -> A) (_39949 : B) : (term557 A B u x''' s _39949) = (term560 A B s u x''' _39949).
Proof. exact (@lem3645710 (term291 B s _39949) (term511 A B u x''' _39949)). Qed.
Lemma lem3645713 (a : Prop) : (term111 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3645714 {B : Type'} (s : B -> Prop) (_39949 : B) : (term547 B s _39949) = (s _39949).
Proof. exact (@lem3645713 (s _39949)). Qed.
Lemma lem3645715 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3645716 {B : Type'} (s : B -> Prop) (_39949 : B) : (term548 B s _39949) = (term160 B s _39949).
Proof. exact (MK_COMB (@lem3645715) (@lem3645714 B s _39949)). Qed.
Lemma lem3645717 {A B : Type'} (u : A -> Prop) (x''' : B -> A) (_39949 : B) : (term511 A B u x''' _39949) = (term511 A B u x''' _39949).
Proof. exact (eq_refl (term511 A B u x''' _39949)). Qed.
Lemma lem3645718 {A B : Type'} (s : B -> Prop) (u : A -> Prop) (x''' : B -> A) (_39949 : B) : (term560 A B s u x''' _39949) = (term561 A B s u x''' _39949).
Proof. exact (MK_COMB (@lem3645716 B s _39949) (@lem3645717 A B u x''' _39949)). Qed.
Lemma lem3645719 {A B : Type'} (s : B -> Prop) (u : A -> Prop) (x''' : B -> A) (_39949 : B) : (term557 A B u x''' s _39949) = (term561 A B s u x''' _39949).
Proof. exact (TRANS (@lem3645711 A B s u x''' _39949) (@lem3645718 A B s u x''' _39949)). Qed.
Lemma lem3645722 {A B : Type'} (_39949 : B) (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term561 A B s u x''' _39949.
Proof. exact (EQ_MP (@lem3645719 A B s u x''' _39949) (@lem3645708 A B _39949 t s f u x''' h1)). Qed.
Lemma lem3645723 {A B : Type'} (_39949 : B) (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term561 A B s u x''' _39949.
Proof. exact (@lem3645722 A B _39949 t s f u x''' h1). Qed.
Lemma lem3645724 {A B : Type'} (x' : B) (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term561 A B s u x''' x'.
Proof. exact (@lem3645723 A B x' t s f u x''' h1). Qed.
Lemma lem3645727 {A B : Type'} (t : A -> Prop) (x''' : B -> A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (h1 : term367 A B t s f u x''') (h2 : term385 A B s x' f u) : term511 A B u x''' x'.
Proof. exact (@lem3645724 A B x' t s f u x''' h1 (@lem3645679 A B s x' f u h2)). Qed.
Lemma lem3645728 {A B : Type'} (t : A -> Prop) (x''' : B -> A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (h1 : term367 A B t s f u x''') (h2 : term385 A B s x' f u) : term562 A B u x''' x'.
Proof. exact (fun h0 : term563 A B u x''' x' => @lem3645727 A B t x''' s x' f u h1 h2). Qed.
Lemma lem3645730 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3645731 {A B : Type'} (u : A -> Prop) (x''' : B -> A) (x' : B) : (term562 A B u x''' x') = (term511 A B u x''' x').
Proof. exact (@lem3645730 (term511 A B u x''' x')). Qed.
Lemma lem3645732 {A B : Type'} (t : A -> Prop) (x''' : B -> A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (h1 : term367 A B t s f u x''') (h2 : term385 A B s x' f u) : term511 A B u x''' x'.
Proof. exact (EQ_MP (@lem3645731 A B u x''' x') (@lem3645728 A B t x''' s x' f u h1 h2)). Qed.
Lemma lem3645734 (a : Prop) (b : Prop) : (term564 a b) = (term565 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3645735 {A B : Type'} (x' : B) (f : A -> B) (u : A -> Prop) (_39950 : A) : (term238 A B x' f u _39950) = (term237 A B x' f u _39950).
Proof. exact (@lem3645734 (x' = (f _39950)) (u _39950)). Qed.
Lemma lem3645737 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3645738 {A B : Type'} (x' : B) (f : A -> B) (u : A -> Prop) (_39950 : A) : (term237 A B x' f u _39950) = (term566 A B x' f u _39950).
Proof. exact (@lem3645737 (term189 A B x' f u _39950)). Qed.
Lemma lem3645739 {A B : Type'} (x' : B) (f : A -> B) (u : A -> Prop) (_39950 : A) : (term238 A B x' f u _39950) = (term566 A B x' f u _39950).
Proof. exact (TRANS (@lem3645735 A B x' f u _39950) (@lem3645738 A B x' f u _39950)). Qed.
Lemma lem3645741 {A B : Type'} (t : A -> Prop) (x''' : B -> A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (h1 : term367 A B t s f u x''') (h2 : term385 A B s x' f u) : term567 A B f u x''' x'.
Proof. exact (conj (@lem3645672 A B t x''' s x' f u h1 h2) (@lem3645732 A B t x''' s x' f u h1 h2)). Qed.
Lemma lem3645743 {A B : Type'} (_39950 : A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (h1 : term385 A B s x' f u) : term566 A B x' f u _39950.
Proof. exact (EQ_MP (@lem3645739 A B x' f u _39950) (@lem3645185 A B _39950 s x' f u h1)). Qed.
Lemma lem3645744 {A B : Type'} (_39950 : A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (h1 : term385 A B s x' f u) : term566 A B x' f u _39950.
Proof. exact (@lem3645743 A B _39950 s x' f u h1). Qed.
Lemma lem3645745 {A B : Type'} (x''' : B -> A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (h1 : term385 A B s x' f u) : term568 A B f u x''' x'.
Proof. exact (@lem3645744 A B (x''' x') s x' f u h1). Qed.
Lemma lem3645748 {A B : Type'} (t : A -> Prop) (x''' : B -> A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (h1 : term367 A B t s f u x''') (h2 : term385 A B s x' f u) : False.
Proof. exact (@lem3645745 A B x''' s x' f u h2 (@lem3645741 A B t x''' s x' f u h1 h2)). Qed.
Lemma lem3645749 {A B : Type'} (t : A -> Prop) (x''' : B -> A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (h1 : term367 A B t s f u x''') (h2 : term385 A B s x' f u) : term117.
Proof. exact (fun h0 : ~ False => @lem3645748 A B t x''' s x' f u h1 h2). Qed.
Lemma lem3645751 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3645752 : term117 = False.
Proof. exact (@lem3645751 False). Qed.
Lemma lem3645753 {A B : Type'} (t : A -> Prop) (x''' : B -> A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (h1 : term367 A B t s f u x''') (h2 : term385 A B s x' f u) : False.
Proof. exact (EQ_MP (@lem3645752) (@lem3645749 A B t x''' s x' f u h1 h2)). Qed.
Lemma lem3645811 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3645812 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3645811 B x). Qed.
Lemma lem3645813 {A B : Type'} (f : A -> B) (x'' : A) : (f x'') = (f x'').
Proof. exact (@lem3645812 B (f x'')). Qed.
Lemma lem3645814 {A B : Type'} (f : A -> B) (x'' : A) : term569 A B f x''.
Proof. exact (fun h0 : term570 A B f x'' => @lem3645813 A B f x''). Qed.
Lemma lem3645816 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3645817 {A B : Type'} (f : A -> B) (x'' : A) : (term569 A B f x'') = ((f x'') = (f x'')).
Proof. exact (@lem3645816 ((f x'') = (f x''))). Qed.
Lemma lem3645818 {A B : Type'} (f : A -> B) (x'' : A) : (f x'') = (f x'').
Proof. exact (EQ_MP (@lem3645817 A B f x'') (@lem3645814 A B f x'')). Qed.
Lemma lem3645820 {A B : Type'} (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (x'' : A) (h1 : term430 A B s x' f u x'') : u x''.
Proof. exact (proj2 (@lem3644616 A B s x' f u x'' h1)). Qed.
Lemma lem3645821 {A B : Type'} (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (x'' : A) (h1 : term430 A B s x' f u x'') : term542 A u x''.
Proof. exact (fun h0 : term291 A u x'' => @lem3645820 A B s x' f u x'' h1). Qed.
Lemma lem3645823 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3645824 {A : Type'} (u : A -> Prop) (x'' : A) : (term542 A u x'') = (u x'').
Proof. exact (@lem3645823 (u x'')). Qed.
Lemma lem3645825 {A B : Type'} (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (x'' : A) (h1 : term430 A B s x' f u x'') : u x''.
Proof. exact (EQ_MP (@lem3645824 A u x'') (@lem3645821 A B s x' f u x'' h1)). Qed.
Lemma lem3645827 (b : Prop) (a : Prop) : (a \/ b) = (term109 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3645828 {A B : Type'} (f : A -> B) (u : A -> Prop) (_39955 : A) (s : B -> Prop) (_39954 : B) : (term524 A B s _39954 f u _39955) = (term571 A B f u _39955 s _39954).
Proof. exact (@lem3645827 (term238 A B _39954 f u _39955) (s _39954)). Qed.
Lemma lem3645830 (a : Prop) (b : Prop) : (term572 a b) = (term573 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3645831 {A B : Type'} (_39954 : B) (f : A -> B) (u : A -> Prop) (_39955 : A) : (term574 A B _39954 f u _39955) = (term575 A B _39954 f u _39955).
Proof. exact (@lem3645830 (term576 A B _39954 f _39955) (term291 A u _39955)). Qed.
Lemma lem3645833 (a : Prop) : (term111 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3645834 {A B : Type'} (_39954 : B) (f : A -> B) (_39955 : A) : (term577 A B _39954 f _39955) = (_39954 = (f _39955)).
Proof. exact (@lem3645833 (_39954 = (f _39955))). Qed.
Lemma lem3645835 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3645836 {A B : Type'} (_39954 : B) (f : A -> B) (_39955 : A) : (term578 A B _39954 f _39955) = (term187 A B _39954 f _39955).
Proof. exact (MK_COMB (@lem3645835) (@lem3645834 A B _39954 f _39955)). Qed.
Lemma lem3645838 (a : Prop) : (term111 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3645839 {A : Type'} (u : A -> Prop) (_39955 : A) : (term547 A u _39955) = (u _39955).
Proof. exact (@lem3645838 (u _39955)). Qed.
Lemma lem3645840 {A B : Type'} (_39954 : B) (f : A -> B) (u : A -> Prop) (_39955 : A) : (term575 A B _39954 f u _39955) = (term189 A B _39954 f u _39955).
Proof. exact (MK_COMB (@lem3645836 A B _39954 f _39955) (@lem3645839 A u _39955)). Qed.
Lemma lem3645841 {A B : Type'} (_39954 : B) (f : A -> B) (u : A -> Prop) (_39955 : A) : (term574 A B _39954 f u _39955) = (term189 A B _39954 f u _39955).
Proof. exact (TRANS (@lem3645831 A B _39954 f u _39955) (@lem3645840 A B _39954 f u _39955)). Qed.
Lemma lem3645842 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3645843 {A B : Type'} (_39954 : B) (f : A -> B) (u : A -> Prop) (_39955 : A) : (term579 A B _39954 f u _39955) = (term580 A B _39954 f u _39955).
Proof. exact (MK_COMB (@lem3645842) (@lem3645841 A B _39954 f u _39955)). Qed.
Lemma lem3645844 {B : Type'} (s : B -> Prop) (_39954 : B) : (s _39954) = (s _39954).
Proof. exact (eq_refl (s _39954)). Qed.
Lemma lem3645845 {A B : Type'} (f : A -> B) (u : A -> Prop) (_39955 : A) (s : B -> Prop) (_39954 : B) : (term571 A B f u _39955 s _39954) = (term581 A B f u _39955 s _39954).
Proof. exact (MK_COMB (@lem3645843 A B _39954 f u _39955) (@lem3645844 B s _39954)). Qed.
Lemma lem3645846 {A B : Type'} (f : A -> B) (u : A -> Prop) (_39955 : A) (s : B -> Prop) (_39954 : B) : (term524 A B s _39954 f u _39955) = (term581 A B f u _39955 s _39954).
Proof. exact (TRANS (@lem3645828 A B f u _39955 s _39954) (@lem3645845 A B f u _39955 s _39954)). Qed.
Lemma lem3645848 {A B : Type'} (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (x'' : A) (h1 : term430 A B s x' f u x'') : term582 A B f u x''.
Proof. exact (conj (@lem3645818 A B f x'') (@lem3645825 A B s x' f u x'' h1)). Qed.
Lemma lem3645850 {A B : Type'} (_39955 : A) (_39954 : B) (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term581 A B f u _39955 s _39954.
Proof. exact (EQ_MP (@lem3645846 A B f u _39955 s _39954) (@lem3645337 A B _39954 _39955 t s f u x''' h1)). Qed.
Lemma lem3645851 {A B : Type'} (_39955 : A) (_39954 : B) (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term581 A B f u _39955 s _39954.
Proof. exact (@lem3645850 A B _39955 _39954 t s f u x''' h1). Qed.
Lemma lem3645852 {A B : Type'} (x'' : A) (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (x''' : B -> A) (h1 : term367 A B t s f u x''') : term583 A B u s f x''.
Proof. exact (@lem3645851 A B x'' (f x'') t s f u x''' h1). Qed.
Lemma lem3645855 {A B : Type'} (t : A -> Prop) (x''' : B -> A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (x'' : A) (h1 : term367 A B t s f u x''') (h2 : term430 A B s x' f u x'') : term584 A B s f x''.
Proof. exact (@lem3645852 A B x'' t s f u x''' h1 (@lem3645848 A B s x' f u x'' h2)). Qed.
Lemma lem3645856 {A B : Type'} (t : A -> Prop) (x''' : B -> A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (x'' : A) (h1 : term367 A B t s f u x''') (h2 : term430 A B s x' f u x'') : term585 A B s f x''.
Proof. exact (fun h0 : term539 A B s f x'' => @lem3645855 A B t x''' s x' f u x'' h1 h2). Qed.
Lemma lem3645858 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3645859 {A B : Type'} (s : B -> Prop) (f : A -> B) (x'' : A) : (term585 A B s f x'') = (term584 A B s f x'').
Proof. exact (@lem3645858 (term584 A B s f x'')). Qed.
Lemma lem3645860 {A B : Type'} (t : A -> Prop) (x''' : B -> A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (x'' : A) (h1 : term367 A B t s f u x''') (h2 : term430 A B s x' f u x'') : term584 A B s f x''.
Proof. exact (EQ_MP (@lem3645859 A B s f x'') (@lem3645856 A B t x''' s x' f u x'' h1 h2)). Qed.
Lemma lem3645863 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3645865 {A B : Type'} (s : B -> Prop) (f : A -> B) (x'' : A) : (term539 A B s f x'') = (term586 A B s f x'').
Proof. exact (@lem3645863 (term584 A B s f x'')). Qed.
Lemma lem3645868 {A B : Type'} (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (x'' : A) (h1 : term430 A B s x' f u x'') : term586 A B s f x''.
Proof. exact (EQ_MP (@lem3645865 A B s f x'') (@lem3645350 A B s x' f u x'' h1)). Qed.
Lemma lem3645871 {A B : Type'} (t : A -> Prop) (x''' : B -> A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (x'' : A) (h1 : term367 A B t s f u x''') (h2 : term430 A B s x' f u x'') : False.
Proof. exact (@lem3645868 A B s x' f u x'' h2 (@lem3645860 A B t x''' s x' f u x'' h1 h2)). Qed.
Lemma lem3645872 {A B : Type'} (t : A -> Prop) (x''' : B -> A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (x'' : A) (h1 : term367 A B t s f u x''') (h2 : term430 A B s x' f u x'') : term117.
Proof. exact (fun h0 : ~ False => @lem3645871 A B t x''' s x' f u x'' h1 h2). Qed.
Lemma lem3645874 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3645875 : term117 = False.
Proof. exact (@lem3645874 False). Qed.
Lemma lem3645877 {A B : Type'} (t : A -> Prop) (x''' : B -> A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (x'' : A) (h1 : term367 A B t s f u x''') (h2 : term430 A B s x' f u x'') : False.
Proof. exact (EQ_MP (@lem3645875) (@lem3645872 A B t x''' s x' f u x'' h1 h2)). Qed.
Lemma lem3645878 {A B : Type'} (t : A -> Prop) (x''' : B -> A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (x'' : A) (h1 : term367 A B t s f u x''') (h2 : term457 A B s x' f u x'') : False.
Proof. exact (or_elim (@lem3644609 A B s x' f u x'' h2) (fun h0 : term385 A B s x' f u => @lem3645753 A B t x''' s x' f u h1 h0) (fun h0 : term430 A B s x' f u x'' => @lem3645877 A B t x''' s x' f u x'' h1 h0)). Qed.
Lemma lem3645879 {A B : Type'} (x''' : B -> A) (t : A -> Prop) (x : A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (x'' : A) (h1 : term367 A B t s f u x''') (h2 : term501 A B t x s x' f u x'') : False.
Proof. exact (or_elim (@lem3644457 A B t x s x' f u x'' h2) (fun h0 : term372 A u t x => @lem3645552 A B s f x''' u t x h1 h0) (fun h0 : term457 A B s x' f u x'' => @lem3645878 A B t x''' s x' f u x'' h1 h0)). Qed.
Lemma lem3645880 {A B : Type'} (x''' : B -> A) (t : A -> Prop) (x : A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (x'' : A) (h1 : term367 A B t s f u x''') (h2 : term501 A B t x s x' f u x'') : (term367 A B t s f u x''') = False.
Proof. exact (prop_ext (fun h3 : term367 A B t s f u x''' => @lem3645879 A B x''' t x s x' f u x'' h1 h2) (fun h3 : False => @lem3644601 A B t s f u x''' h1)). Qed.
Lemma lem3645881 {A B : Type'} (x''' : B -> A) (t : A -> Prop) (x : A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (x'' : A) (h1 : term367 A B t s f u x''') (h2 : term501 A B t x s x' f u x'') : False.
Proof. exact (EQ_MP (@lem3645880 A B x''' t x s x' f u x'' h1 h2) (@lem3644601 A B t s f u x''' h1)). Qed.
Lemma lem3645882 {A B : Type'} (x''' : B -> A) (t : A -> Prop) (x : A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (x'' : A) (h1 : term367 A B t s f u x''') (h2 : term501 A B t x s x' f u x'') : (term501 A B t x s x' f u x'') = False.
Proof. exact (prop_ext (fun h3 : term501 A B t x s x' f u x'' => @lem3645881 A B x''' t x s x' f u x'' h1 h2) (fun h3 : False => @lem3644457 A B t x s x' f u x'' h2)). Qed.
Lemma lem3645883 {A B : Type'} (x''' : B -> A) (t : A -> Prop) (x : A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (x'' : A) (h1 : term367 A B t s f u x''') (h2 : term501 A B t x s x' f u x'') : False.
Proof. exact (EQ_MP (@lem3645882 A B x''' t x s x' f u x'' h1 h2) (@lem3644457 A B t x s x' f u x'' h2)). Qed.
Lemma lem3645884 {A B : Type'} (t : A -> Prop) (x : A) (s : B -> Prop) (x' : B) (f : A -> B) (u : A -> Prop) (x'' : A) (h1 : term197 A B t s f u) (h2 : term501 A B t x s x' f u x'') : False.
Proof. exact (ex_elim (@lem3643948 A B t s f u h1) (fun x''' : B -> A => fun h0 : term369 A B t s f u x''' => @lem3645883 A B x''' t x s x' f u x'' h0 h2)). Qed.
Lemma lem3645885 {A B : Type'} (x : A) (x' : B) (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (h1 : term504 A B t x s x' f u) (h2 : term197 A B t s f u) : False.
Proof. exact (ex_elim (@lem3644390 A B t x s x' f u h1) (fun x'' : A => fun h0 : term503 A B t x s x' f u x'' => @lem3645884 A B t x s x' f u x'' h2 h0)). Qed.
Lemma lem3645886 {A B : Type'} (x : A) (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (h1 : term506 A B t x s f u) (h2 : term197 A B t s f u) : False.
Proof. exact (ex_elim (@lem3644389 A B t x s f u h1) (fun x' : B => fun h0 : term505 A B t x s f u x' => @lem3645885 A B x x' t s f u h0 h2)). Qed.
Lemma lem3645887 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (h1 : term222 A B t s f u) (h2 : term197 A B t s f u) : False.
Proof. exact (ex_elim (@lem3644388 A B t s f u h1) (fun x : A => fun h0 : term507 A B t s f u x => @lem3645886 A B x t s f u h0 h2)). Qed.
Lemma lem3645888 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (h1 : term222 A B t s f u) (h2 : term197 A B t s f u) : (term222 A B t s f u) = False.
Proof. exact (prop_ext (fun h3 : term222 A B t s f u => @lem3645887 A B t s f u h1 h2) (fun h3 : False => @lem3643461 A B t s f u h1)). Qed.
Lemma lem3645889 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (h1 : term222 A B t s f u) (h2 : term197 A B t s f u) : False.
Proof. exact (EQ_MP (@lem3645888 A B t s f u h1 h2) (@lem3643461 A B t s f u h1)). Qed.
Lemma lem3645890 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (h1 : term197 A B t s f u) : term221 A B t s f u.
Proof. exact (fun h0 : term222 A B t s f u => @lem3645889 A B t s f u h0 h1). Qed.
Lemma lem3645891 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) (h1 : term197 A B t s f u) : term199 A B t s f u.
Proof. exact (EQ_MP (@lem3643460 A B t s f u) (@lem3645890 A B t s f u h1)). Qed.
Lemma lem3645892 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (u : A -> Prop) : term200 A B t s f u.
Proof. exact (fun h0 : term197 A B t s f u => @lem3645891 A B t s f u h0). Qed.
Lemma lem3645897 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : term202 A B t s f.
Proof. exact (fun u : A -> Prop => @lem3645892 A B t s f u). Qed.
Lemma lem3645902 {A B : Type'} (s : B -> Prop) (f : A -> B) : term212 A B s f.
Proof. exact (fun t : A -> Prop => @lem3645897 A B t s f). Qed.
Lemma lem3645907 {A B : Type'} (f : A -> B) : term216 A B f.
Proof. exact (fun s : B -> Prop => @lem3645902 A B s f). Qed.
Lemma lem3645912 {A B : Type'} : term220 A B.
Proof. exact (fun f : A -> B => @lem3645907 A B f). Qed.
Lemma lem3645913 {A B : Type'} : term219 A B.
Proof. exact (EQ_MP (@lem3643455 A B) (@lem3645912 A B)). Qed.
Lemma lem3645914 {A B : Type'} (f : A -> B) : term587 A B f.
Proof. exact (@lem3645913 A B f). Qed.
Lemma lem3645915 {A B : Type'} (f : A -> B) : (term587 A B f) = (term215 A B f).
Proof. exact (eq_refl (term587 A B f)). Qed.
Lemma lem3645916 {A B : Type'} (f : A -> B) : term215 A B f.
Proof. exact (EQ_MP (@lem3645915 A B f) (@lem3645914 A B f)). Qed.
Lemma lem3645917 {A B : Type'} (f : A -> B) (s : B -> Prop) : term588 A B f s.
Proof. exact (@lem3645916 A B f s). Qed.
Lemma lem3645918 {A B : Type'} (s : B -> Prop) (f : A -> B) : (term588 A B f s) = (term211 A B s f).
Proof. exact (eq_refl (term588 A B f s)). Qed.
Lemma lem3645919 {A B : Type'} (s : B -> Prop) (f : A -> B) : term211 A B s f.
Proof. exact (EQ_MP (@lem3645918 A B s f) (@lem3645917 A B f s)). Qed.
Lemma lem3645920 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : term589 A B s f t.
Proof. exact (@lem3645919 A B s f t). Qed.
Lemma lem3645921 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term589 A B s f t) = (term203 A B t s f).
Proof. exact (eq_refl (term589 A B s f t)). Qed.
Lemma lem3645922 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : term203 A B t s f.
Proof. exact (EQ_MP (@lem3645921 A B t s f) (@lem3645920 A B s f t)). Qed.
Lemma lem3645924 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : term203 A B t s f.
Proof. exact (@lem3643114 A B t s f (@lem3645922 A B t s f)). Qed.
Lemma lem3645925 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (h1 : term204 A B t s f) : False.
Proof. exact (@lem3645924 A B t s f (@lem3643098 A B t s f h1)). Qed.
Lemma lem3645926 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (h1 : term204 A B t s f) : (term204 A B t s f) = False.
Proof. exact (prop_ext (fun h2 : term204 A B t s f => @lem3645925 A B t s f h1) (fun h2 : False => @lem3643098 A B t s f h1)). Qed.
Lemma lem3645927 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) (h1 : term204 A B t s f) : False.
Proof. exact (EQ_MP (@lem3645926 A B t s f h1) (@lem3643098 A B t s f h1)). Qed.
Lemma lem3645928 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : term203 A B t s f.
Proof. exact (fun h0 : term204 A B t s f => @lem3645927 A B t s f h0). Qed.
Lemma lem3645929 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : term202 A B t s f.
Proof. exact (EQ_MP (@lem3643097 A B t s f) (@lem3645928 A B t s f)). Qed.
Lemma lem3645930 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : term158 A B t s f.
Proof. exact (EQ_MP (@lem3643093 A B t s f) (@lem3645929 A B t s f)). Qed.
Lemma lem3645931 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : term137 A B t s f.
Proof. exact (EQ_MP (@lem3642850 A B t s f) (@lem3645930 A B t s f)). Qed.
Lemma lem3645932 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : term124 A B t s f.
Proof. exact (@lem3642739 A B t s f (@lem3645931 A B t s f)). Qed.
Lemma lem3645933 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : term123 A B t s f.
Proof. exact (EQ_MP (@lem3642712 A B t s f) (@lem3645932 A B t s f)). Qed.
Lemma lem3645934 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : term590 A B s f t.
Proof. exact (conj (@lem3645933 A B t s f) (@lem3642664 A B s f t)). Qed.
Lemma lem3645935 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term590 A B s f t) = ((term10 A B s f t) = (term62 A B t s f)).
Proof. exact (@lem32 (term10 A B s f t) (term62 A B t s f)). Qed.
Lemma lem3645936 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term10 A B s f t) = (term62 A B t s f).
Proof. exact (EQ_MP (@lem3645935 A B t s f) (@lem3645934 A B s f t)). Qed.
Lemma lem3645941 {A B : Type'} (s : B -> Prop) (f : A -> B) : term591 A B s f.
Proof. exact (fun t : A -> Prop => @lem3645936 A B t s f). Qed.
Lemma lem3645946 {A B : Type'} (f : A -> B) : term592 A B f.
Proof. exact (fun s : B -> Prop => @lem3645941 A B s f). Qed.
Lemma lem3645951 {A B : Type'} : term593 A B.
Proof. exact (fun f : A -> B => @lem3645946 A B f). Qed.
