Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTERSECTION_OF_MONO_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import INTERSECTION_OF_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
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
Require Import thm21386_spec.
Lemma lem4844127 {A : Type'} (P : type180 A) : term0 A P.
Proof. exact (@lem4842239 A P). Qed.
Lemma lem4844128 {A : Type'} (P : type180 A) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem4844129 {A : Type'} (P : type180 A) : term1 A P.
Proof. exact (EQ_MP (@lem4844128 A P) (@lem4844127 A P)). Qed.
Lemma lem4844130 {A : Type'} (P : type180 A) (Q : type686 A) : term2 A P Q.
Proof. exact (@lem4844129 A P Q). Qed.
Lemma lem4844131 {A : Type'} (P : type180 A) (Q : type686 A) : (term2 A P Q) = ((@INTERSECTION_OF A P Q) = (term3 A P Q)).
Proof. exact (eq_refl (term2 A P Q)). Qed.
Lemma lem4844154 {A : Type'} (P : type180 A) (Q : type686 A) : (@INTERSECTION_OF A P Q) = (term3 A P Q).
Proof. exact (EQ_MP (@lem4844131 A P Q) (@lem4844130 A P Q)). Qed.
Lemma lem4844155 {A : Type'} (P : type180 A) (Q : type686 A) : (@INTERSECTION_OF A P Q) = (term3 A P Q).
Proof. exact (@lem4844154 A P Q). Qed.
Lemma lem4844172 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4844173 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (@INTERSECTION_OF A P Q s) = (term4 A P Q s).
Proof. exact (MK_COMB (@lem4844155 A P Q) (@lem4844172 A s)). Qed.
Lemma lem4844175 {A B : Type'} (f : A -> B) (y : A) : (term5 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4844176 {A : Type'} (f : type686 A) (y : A -> Prop) : (term6 A f y) = (f y).
Proof. exact (@lem4844175 (A -> Prop) Prop f y). Qed.
Lemma lem4844177 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term7 A P Q s) = (term4 A P Q s).
Proof. exact (@lem4844176 A (term3 A P Q) s). Qed.
Lemma lem4844178 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term4 A P Q s) = (term8 A P Q s).
Proof. exact (eq_refl (term4 A P Q s)). Qed.
Lemma lem4844179 {A : Type'} (P : type180 A) (Q : type686 A) : (term9 A P Q) = (term3 A P Q).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4844178 A P Q s)). Qed.
Lemma lem4844180 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4844181 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term7 A P Q s) = (term4 A P Q s).
Proof. exact (MK_COMB (@lem4844179 A P Q) (@lem4844180 A s)). Qed.
Lemma lem4844182 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4844183 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term10 A P Q s) = (term11 A P Q s).
Proof. exact (MK_COMB (@lem4844182) (@lem4844181 A P Q s)). Qed.
Lemma lem4844184 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term4 A P Q s) = (term8 A P Q s).
Proof. exact (eq_refl (term4 A P Q s)). Qed.
Lemma lem4844185 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : ((term7 A P Q s) = (term4 A P Q s)) = ((term4 A P Q s) = (term8 A P Q s)).
Proof. exact (MK_COMB (@lem4844183 A P Q s) (@lem4844184 A P Q s)). Qed.
Lemma lem4844186 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term4 A P Q s) = (term8 A P Q s).
Proof. exact (EQ_MP (@lem4844185 A P Q s) (@lem4844177 A P Q s)). Qed.
Lemma lem4844203 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (@INTERSECTION_OF A P Q s) = (term8 A P Q s).
Proof. exact (TRANS (@lem4844173 A P Q s) (@lem4844186 A P Q s)). Qed.
Lemma lem4844204 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4844205 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term12 A P Q s) = (term13 A P Q s).
Proof. exact (MK_COMB (@lem4844204) (@lem4844203 A P Q s)). Qed.
Lemma lem4844212 {A : Type'} (Q : type686 A) (Q' : type686 A) : (term14 A Q Q') = (term14 A Q Q').
Proof. exact (eq_refl (term14 A Q Q')). Qed.
Lemma lem4844213 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) : (term15 A P s Q Q') = (term16 A P s Q Q').
Proof. exact (MK_COMB (@lem4844205 A P Q s) (@lem4844212 A Q Q')). Qed.
Lemma lem4844216 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4844217 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) : (term17 A P s Q Q') = (term18 A P s Q Q').
Proof. exact (MK_COMB (@lem4844216) (@lem4844213 A P s Q Q')). Qed.
Lemma lem4844219 {A : Type'} (P : type180 A) (Q : type686 A) : (@INTERSECTION_OF A P Q) = (term3 A P Q).
Proof. exact (EQ_MP (@lem4844131 A P Q) (@lem4844130 A P Q)). Qed.
Lemma lem4844220 {A : Type'} (P : type180 A) (Q : type686 A) : (@INTERSECTION_OF A P Q) = (term3 A P Q).
Proof. exact (@lem4844219 A P Q). Qed.
Lemma lem4844221 {A : Type'} (P : type180 A) (Q' : type686 A) : (@INTERSECTION_OF A P Q') = (term3 A P Q').
Proof. exact (@lem4844220 A P Q'). Qed.
Lemma lem4844238 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4844239 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (@INTERSECTION_OF A P Q' s) = (term4 A P Q' s).
Proof. exact (MK_COMB (@lem4844221 A P Q') (@lem4844238 A s)). Qed.
Lemma lem4844241 {A B : Type'} (f : A -> B) (y : A) : (term5 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4844242 {A : Type'} (f : type686 A) (y : A -> Prop) : (term6 A f y) = (f y).
Proof. exact (@lem4844241 (A -> Prop) Prop f y). Qed.
Lemma lem4844243 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term7 A P Q' s) = (term4 A P Q' s).
Proof. exact (@lem4844242 A (term3 A P Q') s). Qed.
Lemma lem4844244 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term4 A P Q' s) = (term8 A P Q' s).
Proof. exact (eq_refl (term4 A P Q' s)). Qed.
Lemma lem4844245 {A : Type'} (P : type180 A) (Q' : type686 A) : (term9 A P Q') = (term3 A P Q').
Proof. exact (fun_ext (fun s : A -> Prop => @lem4844244 A P Q' s)). Qed.
Lemma lem4844246 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4844247 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term7 A P Q' s) = (term4 A P Q' s).
Proof. exact (MK_COMB (@lem4844245 A P Q') (@lem4844246 A s)). Qed.
Lemma lem4844248 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4844249 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term10 A P Q' s) = (term11 A P Q' s).
Proof. exact (MK_COMB (@lem4844248) (@lem4844247 A P Q' s)). Qed.
Lemma lem4844250 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term4 A P Q' s) = (term8 A P Q' s).
Proof. exact (eq_refl (term4 A P Q' s)). Qed.
Lemma lem4844251 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : ((term7 A P Q' s) = (term4 A P Q' s)) = ((term4 A P Q' s) = (term8 A P Q' s)).
Proof. exact (MK_COMB (@lem4844249 A P Q' s) (@lem4844250 A P Q' s)). Qed.
Lemma lem4844252 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term4 A P Q' s) = (term8 A P Q' s).
Proof. exact (EQ_MP (@lem4844251 A P Q' s) (@lem4844243 A P Q' s)). Qed.
Lemma lem4844269 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (@INTERSECTION_OF A P Q' s) = (term8 A P Q' s).
Proof. exact (TRANS (@lem4844239 A P Q' s) (@lem4844252 A P Q' s)). Qed.
Lemma lem4844270 {A : Type'} (Q : type686 A) (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term19 A Q P Q' s) = (term20 A Q P Q' s).
Proof. exact (MK_COMB (@lem4844217 A P s Q Q') (@lem4844269 A P Q' s)). Qed.
Lemma lem4844273 {A : Type'} (Q : type686 A) (P : type180 A) (Q' : type686 A) : (term21 A Q P Q') = (term22 A Q P Q').
Proof. exact (fun_ext (fun s : A -> Prop => @lem4844270 A Q P Q' s)). Qed.
Lemma lem4844274 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4844275 {A : Type'} (Q : type686 A) (P : type180 A) (Q' : type686 A) : (term23 A Q P Q') = (term24 A Q P Q').
Proof. exact (MK_COMB (@lem4844274 A) (@lem4844273 A Q P Q')). Qed.
Lemma lem4844280 {A : Type'} (Q : type686 A) (P : type180 A) : (term25 A Q P) = (term26 A Q P).
Proof. exact (fun_ext (fun Q' : type686 A => @lem4844275 A Q P Q')). Qed.
Lemma lem4844281 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4844282 {A : Type'} (Q : type686 A) (P : type180 A) : (term27 A Q P) = (term28 A Q P).
Proof. exact (MK_COMB (@lem4844281 A) (@lem4844280 A Q P)). Qed.
Lemma lem4844287 {A : Type'} (P : type180 A) : (term29 A P) = (term30 A P).
Proof. exact (fun_ext (fun Q : type686 A => @lem4844282 A Q P)). Qed.
Lemma lem4844288 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4844289 {A : Type'} (P : type180 A) : (term31 A P) = (term32 A P).
Proof. exact (MK_COMB (@lem4844288 A) (@lem4844287 A P)). Qed.
Lemma lem4844294 {A : Type'} : (term33 A) = (term34 A).
Proof. exact (fun_ext (fun P : type180 A => @lem4844289 A P)). Qed.
Lemma lem4844295 {A : Type'} : (@all (((A -> Prop) -> Prop) -> Prop)) = (@all (((A -> Prop) -> Prop) -> Prop)).
Proof. exact (eq_refl (@all (((A -> Prop) -> Prop) -> Prop))). Qed.
Lemma lem4844296 {A : Type'} : (term35 A) = (term36 A).
Proof. exact (MK_COMB (@lem4844295 A) (@lem4844294 A)). Qed.
Lemma lem4844301 {A : Type'} : (term36 A) = (term35 A).
Proof. exact (SYM (@lem4844296 A)). Qed.
Lemma lem4844303 (p : Prop) : p = (term37 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4844304 {A : Type'} : (term36 A) = (term38 A).
Proof. exact (@lem4844303 (term36 A)). Qed.
Lemma lem4844305 {A : Type'} : (term38 A) = (term36 A).
Proof. exact (SYM (@lem4844304 A)). Qed.
Lemma lem4844306 {A : Type'} (h1 : term39 A) : term39 A.
Proof. exact (h1). Qed.
Lemma lem4844309 {A : Type'} (h1 : term38 A) : term38 A.
Proof. exact (h1). Qed.
Lemma lem4844310 {A : Type'} : term40 A.
Proof. exact (fun h0 : term38 A => @lem4844309 A h0). Qed.
Lemma lem4844311 {A : Type'} (h1 : term40 A) : term40 A.
Proof. exact (h1). Qed.
Lemma lem4844312 {A : Type'} (h1 : term38 A) : term38 A.
Proof. exact (h1). Qed.
Lemma lem4844313 {A : Type'} (h1 : term38 A) (h2 : term40 A) : term38 A.
Proof. exact (@lem4844311 A h2 (@lem4844312 A h1)). Qed.
Lemma lem4844314 {A : Type'} (h1 : term38 A) : term41 A.
Proof. exact (fun h0 : term40 A => @lem4844313 A h1 h0). Qed.
Lemma lem4844315 {A : Type'} (h1 : term40 A) : term40 A.
Proof. exact (h1). Qed.
Lemma lem4844316 {A : Type'} (h1 : term38 A) (h2 : term40 A) : term38 A.
Proof. exact (@lem4844314 A h1 (@lem4844315 A h2)). Qed.
Lemma lem4844317 {A : Type'} (h1 : term40 A) : term40 A.
Proof. exact (fun h0 : term38 A => @lem4844316 A h0 h1). Qed.
Lemma lem4844318 {A : Type'} : term42 A.
Proof. exact (fun h0 : term40 A => @lem4844317 A h0). Qed.
Lemma lem4844321 {A : Type'} : term40 A.
Proof. exact (@lem4844318 A (@lem4844310 A)). Qed.
Lemma lem4844322 {A : Type'} : term40 A.
Proof. exact (@lem4844321 A). Qed.
Lemma lem4844324 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4844325 {A : Type'} : (term38 A) = (term43 A).
Proof. exact (@lem4844324 (term39 A)). Qed.
Lemma lem4844327 (t : Prop) : (term44 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4844328 {A : Type'} : (term43 A) = (term36 A).
Proof. exact (@lem4844327 (term36 A)). Qed.
Lemma lem4844435 {A : Type'} : (term38 A) = (term36 A).
Proof. exact (TRANS (@lem4844325 A) (@lem4844328 A)). Qed.
Lemma lem4844436 {A : Type'} (u : type686 A) (s : A -> Prop) : ((@INTERS A u) = s) = ((@INTERS A u) = s).
Proof. exact (eq_refl ((@INTERS A u) = s)). Qed.
Lemma lem4844441 {A : Type'} (u : type686 A) (Q' : type686 A) (c : A -> Prop) : (term45 A u Q' c) = (term45 A u Q' c).
Proof. exact (eq_refl (term45 A u Q' c)). Qed.
Lemma lem4844442 {A : Type'} (u : type686 A) (Q' : type686 A) : (term46 A u Q') = (term46 A u Q').
Proof. exact (fun_ext (fun c : A -> Prop => @lem4844441 A u Q' c)). Qed.
Lemma lem4844443 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4844444 {A : Type'} (u : type686 A) (Q' : type686 A) : (term47 A u Q') = (term47 A u Q').
Proof. exact (MK_COMB (@lem4844443 A) (@lem4844442 A u Q')). Qed.
Lemma lem4844445 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4844446 {A : Type'} (u : type686 A) (Q' : type686 A) : (term48 A u Q') = (term48 A u Q').
Proof. exact (MK_COMB (@lem4844445) (@lem4844444 A u Q')). Qed.
Lemma lem4844447 {A : Type'} (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term49 A Q' u s) = (term49 A Q' u s).
Proof. exact (MK_COMB (@lem4844446 A u Q') (@lem4844436 A u s)). Qed.
Lemma lem4844450 {A : Type'} (P : type180 A) (u : type686 A) : (term50 A P u) = (term50 A P u).
Proof. exact (eq_refl (term50 A P u)). Qed.
Lemma lem4844451 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term51 A P Q' u s) = (term51 A P Q' u s).
Proof. exact (MK_COMB (@lem4844450 A P u) (@lem4844447 A Q' u s)). Qed.
Lemma lem4844452 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term52 A P Q' s) = (term52 A P Q' s).
Proof. exact (fun_ext (fun u : type686 A => @lem4844451 A P Q' u s)). Qed.
Lemma lem4844453 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4844454 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term8 A P Q' s) = (term8 A P Q' s).
Proof. exact (MK_COMB (@lem4844453 A) (@lem4844452 A P Q' s)). Qed.
Lemma lem4844459 {A : Type'} (Q : type686 A) (Q' : type686 A) (x : A -> Prop) : (term53 A Q Q' x) = (term53 A Q Q' x).
Proof. exact (eq_refl (term53 A Q Q' x)). Qed.
Lemma lem4844460 {A : Type'} (Q : type686 A) (Q' : type686 A) : (term54 A Q Q') = (term54 A Q Q').
Proof. exact (fun_ext (fun x : A -> Prop => @lem4844459 A Q Q' x)). Qed.
Lemma lem4844461 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4844462 {A : Type'} (Q : type686 A) (Q' : type686 A) : (term14 A Q Q') = (term14 A Q Q').
Proof. exact (MK_COMB (@lem4844461 A) (@lem4844460 A Q Q')). Qed.
Lemma lem4844463 {A : Type'} (u : type686 A) (s : A -> Prop) : ((@INTERS A u) = s) = ((@INTERS A u) = s).
Proof. exact (eq_refl ((@INTERS A u) = s)). Qed.
Lemma lem4844468 {A : Type'} (u : type686 A) (Q : type686 A) (c : A -> Prop) : (term45 A u Q c) = (term45 A u Q c).
Proof. exact (eq_refl (term45 A u Q c)). Qed.
Lemma lem4844469 {A : Type'} (u : type686 A) (Q : type686 A) : (term46 A u Q) = (term46 A u Q).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4844468 A u Q c)). Qed.
Lemma lem4844470 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4844471 {A : Type'} (u : type686 A) (Q : type686 A) : (term47 A u Q) = (term47 A u Q).
Proof. exact (MK_COMB (@lem4844470 A) (@lem4844469 A u Q)). Qed.
Lemma lem4844472 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4844473 {A : Type'} (u : type686 A) (Q : type686 A) : (term48 A u Q) = (term48 A u Q).
Proof. exact (MK_COMB (@lem4844472) (@lem4844471 A u Q)). Qed.
Lemma lem4844474 {A : Type'} (Q : type686 A) (u : type686 A) (s : A -> Prop) : (term49 A Q u s) = (term49 A Q u s).
Proof. exact (MK_COMB (@lem4844473 A u Q) (@lem4844463 A u s)). Qed.
Lemma lem4844477 {A : Type'} (P : type180 A) (u : type686 A) : (term50 A P u) = (term50 A P u).
Proof. exact (eq_refl (term50 A P u)). Qed.
Lemma lem4844478 {A : Type'} (P : type180 A) (Q : type686 A) (u : type686 A) (s : A -> Prop) : (term51 A P Q u s) = (term51 A P Q u s).
Proof. exact (MK_COMB (@lem4844477 A P u) (@lem4844474 A Q u s)). Qed.
Lemma lem4844479 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term52 A P Q s) = (term52 A P Q s).
Proof. exact (fun_ext (fun u : type686 A => @lem4844478 A P Q u s)). Qed.
Lemma lem4844480 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4844481 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term8 A P Q s) = (term8 A P Q s).
Proof. exact (MK_COMB (@lem4844480 A) (@lem4844479 A P Q s)). Qed.
Lemma lem4844482 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4844483 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term13 A P Q s) = (term13 A P Q s).
Proof. exact (MK_COMB (@lem4844482) (@lem4844481 A P Q s)). Qed.
Lemma lem4844484 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) : (term16 A P s Q Q') = (term16 A P s Q Q').
Proof. exact (MK_COMB (@lem4844483 A P Q s) (@lem4844462 A Q Q')). Qed.
Lemma lem4844485 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4844486 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) : (term18 A P s Q Q') = (term18 A P s Q Q').
Proof. exact (MK_COMB (@lem4844485) (@lem4844484 A P s Q Q')). Qed.
Lemma lem4844487 {A : Type'} (Q : type686 A) (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term20 A Q P Q' s) = (term20 A Q P Q' s).
Proof. exact (MK_COMB (@lem4844486 A P s Q Q') (@lem4844454 A P Q' s)). Qed.
Lemma lem4844488 {A : Type'} (Q : type686 A) (P : type180 A) (Q' : type686 A) : (term22 A Q P Q') = (term22 A Q P Q').
Proof. exact (fun_ext (fun s : A -> Prop => @lem4844487 A Q P Q' s)). Qed.
Lemma lem4844489 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4844490 {A : Type'} (Q : type686 A) (P : type180 A) (Q' : type686 A) : (term24 A Q P Q') = (term24 A Q P Q').
Proof. exact (MK_COMB (@lem4844489 A) (@lem4844488 A Q P Q')). Qed.
Lemma lem4844491 {A : Type'} (Q : type686 A) (P : type180 A) : (term26 A Q P) = (term26 A Q P).
Proof. exact (fun_ext (fun Q' : type686 A => @lem4844490 A Q P Q')). Qed.
Lemma lem4844492 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4844493 {A : Type'} (Q : type686 A) (P : type180 A) : (term28 A Q P) = (term28 A Q P).
Proof. exact (MK_COMB (@lem4844492 A) (@lem4844491 A Q P)). Qed.
Lemma lem4844494 {A : Type'} (P : type180 A) : (term30 A P) = (term30 A P).
Proof. exact (fun_ext (fun Q : type686 A => @lem4844493 A Q P)). Qed.
Lemma lem4844495 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4844496 {A : Type'} (P : type180 A) : (term32 A P) = (term32 A P).
Proof. exact (MK_COMB (@lem4844495 A) (@lem4844494 A P)). Qed.
Lemma lem4844497 {A : Type'} : (term34 A) = (term34 A).
Proof. exact (fun_ext (fun P : type180 A => @lem4844496 A P)). Qed.
Lemma lem4844498 {A : Type'} : (@all (((A -> Prop) -> Prop) -> Prop)) = (@all (((A -> Prop) -> Prop) -> Prop)).
Proof. exact (eq_refl (@all (((A -> Prop) -> Prop) -> Prop))). Qed.
Lemma lem4844499 {A : Type'} : (term36 A) = (term36 A).
Proof. exact (MK_COMB (@lem4844498 A) (@lem4844497 A)). Qed.
Lemma lem4844574 {A : Type'} : (term38 A) = (term36 A).
Proof. exact (TRANS (@lem4844435 A) (@lem4844499 A)). Qed.
Lemma lem4844575 {A : Type'} : (term36 A) = (term38 A).
Proof. exact (SYM (@lem4844574 A)). Qed.
Lemma lem4844576 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term16 A P s Q Q') : term16 A P s Q Q'.
Proof. exact (h1). Qed.
Lemma lem4844578 (p : Prop) : p = (term37 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4844579 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term8 A P Q' s) = (term55 A P Q' s).
Proof. exact (@lem4844578 (term8 A P Q' s)). Qed.
Lemma lem4844580 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term55 A P Q' s) = (term8 A P Q' s).
Proof. exact (SYM (@lem4844579 A P Q' s)). Qed.
Lemma lem4844581 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) (h1 : term56 A P Q' s) : term56 A P Q' s.
Proof. exact (h1). Qed.
Lemma lem4844589 {A : Type'} (u : type686 A) (Q : type686 A) (c : A -> Prop) : (term45 A u Q c) = (term57 A u Q c).
Proof. exact (@lem17265 (@IN (A -> Prop) c u) (Q c)). Qed.
Lemma lem4844590 {A : Type'} (u : type686 A) (Q : type686 A) : (term46 A u Q) = (term58 A u Q).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4844589 A u Q c)). Qed.
Lemma lem4844591 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4844592 {A : Type'} (u : type686 A) (Q : type686 A) : (term47 A u Q) = (term59 A u Q).
Proof. exact (MK_COMB (@lem4844591 A) (@lem4844590 A u Q)). Qed.
Lemma lem4844593 {A : Type'} (u : type686 A) (s : A -> Prop) : ((@INTERS A u) = s) = ((@INTERS A u) = s).
Proof. exact (eq_refl ((@INTERS A u) = s)). Qed.
Lemma lem4844594 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4844595 {A : Type'} (u : type686 A) (Q : type686 A) : (term48 A u Q) = (term60 A u Q).
Proof. exact (MK_COMB (@lem4844594) (@lem4844592 A u Q)). Qed.
Lemma lem4844596 {A : Type'} (Q : type686 A) (u : type686 A) (s : A -> Prop) : (term49 A Q u s) = (term61 A Q u s).
Proof. exact (MK_COMB (@lem4844595 A u Q) (@lem4844593 A u s)). Qed.
Lemma lem4844598 {A : Type'} (P : type180 A) (u : type686 A) : (term50 A P u) = (term50 A P u).
Proof. exact (eq_refl (term50 A P u)). Qed.
Lemma lem4844599 {A : Type'} (P : type180 A) (Q : type686 A) (u : type686 A) (s : A -> Prop) : (term51 A P Q u s) = (term62 A P Q u s).
Proof. exact (MK_COMB (@lem4844598 A P u) (@lem4844596 A Q u s)). Qed.
Lemma lem4844600 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term52 A P Q s) = (term63 A P Q s).
Proof. exact (fun_ext (fun u : type686 A => @lem4844599 A P Q u s)). Qed.
Lemma lem4844601 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4844602 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term8 A P Q s) = (term64 A P Q s).
Proof. exact (MK_COMB (@lem4844601 A) (@lem4844600 A P Q s)). Qed.
Lemma lem4844609 {A : Type'} (Q : type686 A) (Q' : type686 A) (x : A -> Prop) : (term53 A Q Q' x) = (term65 A Q Q' x).
Proof. exact (@lem17265 (Q x) (Q' x)). Qed.
Lemma lem4844610 {A : Type'} (Q : type686 A) (Q' : type686 A) : (term54 A Q Q') = (term66 A Q Q').
Proof. exact (fun_ext (fun x : A -> Prop => @lem4844609 A Q Q' x)). Qed.
Lemma lem4844611 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4844612 {A : Type'} (Q : type686 A) (Q' : type686 A) : (term14 A Q Q') = (term67 A Q Q').
Proof. exact (MK_COMB (@lem4844611 A) (@lem4844610 A Q Q')). Qed.
Lemma lem4844613 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4844614 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term13 A P Q s) = (term68 A P Q s).
Proof. exact (MK_COMB (@lem4844613) (@lem4844602 A P Q s)). Qed.
Lemma lem4844615 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) : (term16 A P s Q Q') = (term69 A P s Q Q').
Proof. exact (MK_COMB (@lem4844614 A P Q s) (@lem4844612 A Q Q')). Qed.
Lemma lem4844710 {A : Type'} (P : A -> Prop) (Q : Prop) : (term70 A P Q) = (term71 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4844711 {A : Type'} (P : type180 A) (Q : Prop) : (term72 A P Q) = (term73 A P Q).
Proof. exact (@lem4844710 (type686 A) P Q). Qed.
Lemma lem4844712 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) : (term74 A P s Q Q') = (term75 A P s Q Q').
Proof. exact (@lem4844711 A (term63 A P Q s) (term67 A Q Q')). Qed.
Lemma lem4844713 {A : Type'} (P : type180 A) (Q : type686 A) (u : type686 A) (s : A -> Prop) : (term76 A P Q s u) = (term62 A P Q u s).
Proof. exact (eq_refl (term76 A P Q s u)). Qed.
Lemma lem4844714 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term77 A P Q s) = (term63 A P Q s).
Proof. exact (fun_ext (fun u : type686 A => @lem4844713 A P Q u s)). Qed.
Lemma lem4844715 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4844716 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term78 A P Q s) = (term64 A P Q s).
Proof. exact (MK_COMB (@lem4844715 A) (@lem4844714 A P Q s)). Qed.
Lemma lem4844717 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4844718 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term79 A P Q s) = (term68 A P Q s).
Proof. exact (MK_COMB (@lem4844717) (@lem4844716 A P Q s)). Qed.
Lemma lem4844719 {A : Type'} (Q : type686 A) (Q' : type686 A) : (term67 A Q Q') = (term67 A Q Q').
Proof. exact (eq_refl (term67 A Q Q')). Qed.
Lemma lem4844720 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) : (term74 A P s Q Q') = (term69 A P s Q Q').
Proof. exact (MK_COMB (@lem4844718 A P Q s) (@lem4844719 A Q Q')). Qed.
Lemma lem4844721 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4844722 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) : (term80 A P s Q Q') = (term81 A P s Q Q').
Proof. exact (MK_COMB (@lem4844721) (@lem4844720 A P s Q Q')). Qed.
Lemma lem4844723 {A : Type'} (P : type180 A) (Q : type686 A) (u : type686 A) (s : A -> Prop) : (term76 A P Q s u) = (term62 A P Q u s).
Proof. exact (eq_refl (term76 A P Q s u)). Qed.
Lemma lem4844724 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4844725 {A : Type'} (P : type180 A) (Q : type686 A) (u : type686 A) (s : A -> Prop) : (term82 A P Q s u) = (term83 A P Q u s).
Proof. exact (MK_COMB (@lem4844724) (@lem4844723 A P Q u s)). Qed.
Lemma lem4844726 {A : Type'} (Q : type686 A) (Q' : type686 A) : (term67 A Q Q') = (term67 A Q Q').
Proof. exact (eq_refl (term67 A Q Q')). Qed.
Lemma lem4844727 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) : (term84 A P s u Q Q') = (term85 A P u s Q Q').
Proof. exact (MK_COMB (@lem4844725 A P Q u s) (@lem4844726 A Q Q')). Qed.
Lemma lem4844728 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) : (term86 A P s Q Q') = (term87 A P s Q Q').
Proof. exact (fun_ext (fun u : type686 A => @lem4844727 A P u s Q Q')). Qed.
Lemma lem4844729 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4844730 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) : (term75 A P s Q Q') = (term88 A P s Q Q').
Proof. exact (MK_COMB (@lem4844729 A) (@lem4844728 A P s Q Q')). Qed.
Lemma lem4844731 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) : ((term74 A P s Q Q') = (term75 A P s Q Q')) = ((term69 A P s Q Q') = (term88 A P s Q Q')).
Proof. exact (MK_COMB (@lem4844722 A P s Q Q') (@lem4844730 A P s Q Q')). Qed.
Lemma lem4844733 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) : (term69 A P s Q Q') = (term88 A P s Q Q').
Proof. exact (EQ_MP (@lem4844731 A P s Q Q') (@lem4844712 A P s Q Q')). Qed.
Lemma lem4844734 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) : (term16 A P s Q Q') = (term88 A P s Q Q').
Proof. exact (TRANS (@lem4844615 A P s Q Q') (@lem4844733 A P s Q Q')). Qed.
Lemma lem4844735 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term16 A P s Q Q') : term88 A P s Q Q'.
Proof. exact (EQ_MP (@lem4844734 A P s Q Q') (@lem4844576 A P s Q Q' h1)). Qed.
Lemma lem4844743 {A : Type'} (u : type686 A) (Q' : type686 A) (c : A -> Prop) : (term89 A u Q' c) = (term90 A u Q' c).
Proof. exact (@lem17362 (@IN (A -> Prop) c u) (Q' c)). Qed.
Lemma lem4844744 {A : Type'} (P : type686 A) : (term91 A P) = (term92 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem4844745 {A : Type'} (u : type686 A) (Q' : type686 A) : (term93 A u Q') = (term94 A u Q').
Proof. exact (@lem4844744 A (term46 A u Q')). Qed.
Lemma lem4844746 {A : Type'} (u : type686 A) (Q' : type686 A) (c : A -> Prop) : (term95 A u Q' c) = (term45 A u Q' c).
Proof. exact (eq_refl (term95 A u Q' c)). Qed.
Lemma lem4844747 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4844748 {A : Type'} (u : type686 A) (Q' : type686 A) (c : A -> Prop) : (term96 A u Q' c) = (term89 A u Q' c).
Proof. exact (MK_COMB (@lem4844747) (@lem4844746 A u Q' c)). Qed.
Lemma lem4844749 {A : Type'} (u : type686 A) (Q' : type686 A) (c : A -> Prop) : (term96 A u Q' c) = (term90 A u Q' c).
Proof. exact (TRANS (@lem4844748 A u Q' c) (@lem4844743 A u Q' c)). Qed.
Lemma lem4844750 {A : Type'} (u : type686 A) (Q' : type686 A) : (term97 A u Q') = (term98 A u Q').
Proof. exact (fun_ext (fun c : A -> Prop => @lem4844749 A u Q' c)). Qed.
Lemma lem4844751 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4844752 {A : Type'} (u : type686 A) (Q' : type686 A) : (term94 A u Q') = (term99 A u Q').
Proof. exact (MK_COMB (@lem4844751 A) (@lem4844750 A u Q')). Qed.
Lemma lem4844753 {A : Type'} (u : type686 A) (Q' : type686 A) : (term93 A u Q') = (term99 A u Q').
Proof. exact (TRANS (@lem4844745 A u Q') (@lem4844752 A u Q')). Qed.
Lemma lem4844754 {A : Type'} (u : type686 A) (s : A -> Prop) : (term100 A u s) = (term100 A u s).
Proof. exact (eq_refl (term100 A u s)). Qed.
Lemma lem4844755 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4844756 {A : Type'} (u : type686 A) (Q' : type686 A) : (term101 A u Q') = (term102 A u Q').
Proof. exact (MK_COMB (@lem4844755) (@lem4844753 A u Q')). Qed.
Lemma lem4844757 {A : Type'} (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term103 A Q' u s) = (term104 A Q' u s).
Proof. exact (MK_COMB (@lem4844756 A u Q') (@lem4844754 A u s)). Qed.
Lemma lem4844758 {A : Type'} (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term105 A Q' u s) = (term103 A Q' u s).
Proof. exact (@lem17045 (term47 A u Q') ((@INTERS A u) = s)). Qed.
Lemma lem4844759 {A : Type'} (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term105 A Q' u s) = (term104 A Q' u s).
Proof. exact (TRANS (@lem4844758 A Q' u s) (@lem4844757 A Q' u s)). Qed.
Lemma lem4844761 {A : Type'} (P : type180 A) (u : type686 A) : (term106 A P u) = (term106 A P u).
Proof. exact (eq_refl (term106 A P u)). Qed.
Lemma lem4844762 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term107 A P Q' u s) = (term108 A P Q' u s).
Proof. exact (MK_COMB (@lem4844761 A P u) (@lem4844759 A Q' u s)). Qed.
Lemma lem4844763 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term109 A P Q' u s) = (term107 A P Q' u s).
Proof. exact (@lem17045 (P u) (term49 A Q' u s)). Qed.
Lemma lem4844764 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term109 A P Q' u s) = (term108 A P Q' u s).
Proof. exact (TRANS (@lem4844763 A P Q' u s) (@lem4844762 A P Q' u s)). Qed.
Lemma lem4844765 {A : Type'} (P : type180 A) : (term110 A P) = (term111 A P).
Proof. exact (@lem18394 (type686 A) P). Qed.
Lemma lem4844766 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term56 A P Q' s) = (term112 A P Q' s).
Proof. exact (@lem4844765 A (term52 A P Q' s)). Qed.
Lemma lem4844767 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term113 A P Q' s u) = (term51 A P Q' u s).
Proof. exact (eq_refl (term113 A P Q' s u)). Qed.
Lemma lem4844768 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4844769 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term114 A P Q' s u) = (term109 A P Q' u s).
Proof. exact (MK_COMB (@lem4844768) (@lem4844767 A P Q' u s)). Qed.
Lemma lem4844770 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term114 A P Q' s u) = (term108 A P Q' u s).
Proof. exact (TRANS (@lem4844769 A P Q' u s) (@lem4844764 A P Q' u s)). Qed.
Lemma lem4844771 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term115 A P Q' s) = (term116 A P Q' s).
Proof. exact (fun_ext (fun u : type686 A => @lem4844770 A P Q' u s)). Qed.
Lemma lem4844772 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4844773 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term112 A P Q' s) = (term117 A P Q' s).
Proof. exact (MK_COMB (@lem4844772 A) (@lem4844771 A P Q' s)). Qed.
Lemma lem4844774 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term56 A P Q' s) = (term117 A P Q' s).
Proof. exact (TRANS (@lem4844766 A P Q' s) (@lem4844773 A P Q' s)). Qed.
Lemma lem4844873 {A : Type'} (P : A -> Prop) (Q : Prop) : (term118 A P Q) = (term119 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4844874 {A : Type'} (P : type686 A) (Q : Prop) : (term120 A P Q) = (term121 A P Q).
Proof. exact (@lem4844873 (A -> Prop) P Q). Qed.
Lemma lem4844875 {A : Type'} (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term122 A Q' u s) = (term123 A Q' u s).
Proof. exact (@lem4844874 A (term98 A u Q') (term100 A u s)). Qed.
Lemma lem4844876 {A : Type'} (u : type686 A) (Q' : type686 A) (c : A -> Prop) : (term124 A u Q' c) = (term90 A u Q' c).
Proof. exact (eq_refl (term124 A u Q' c)). Qed.
Lemma lem4844877 {A : Type'} (u : type686 A) (Q' : type686 A) : (term125 A u Q') = (term98 A u Q').
Proof. exact (fun_ext (fun c : A -> Prop => @lem4844876 A u Q' c)). Qed.
Lemma lem4844878 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4844879 {A : Type'} (u : type686 A) (Q' : type686 A) : (term126 A u Q') = (term99 A u Q').
Proof. exact (MK_COMB (@lem4844878 A) (@lem4844877 A u Q')). Qed.
Lemma lem4844880 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4844881 {A : Type'} (u : type686 A) (Q' : type686 A) : (term127 A u Q') = (term102 A u Q').
Proof. exact (MK_COMB (@lem4844880) (@lem4844879 A u Q')). Qed.
Lemma lem4844882 {A : Type'} (u : type686 A) (s : A -> Prop) : (term100 A u s) = (term100 A u s).
Proof. exact (eq_refl (term100 A u s)). Qed.
Lemma lem4844883 {A : Type'} (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term122 A Q' u s) = (term104 A Q' u s).
Proof. exact (MK_COMB (@lem4844881 A u Q') (@lem4844882 A u s)). Qed.
Lemma lem4844884 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4844885 {A : Type'} (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term128 A Q' u s) = (term129 A Q' u s).
Proof. exact (MK_COMB (@lem4844884) (@lem4844883 A Q' u s)). Qed.
Lemma lem4844886 {A : Type'} (u : type686 A) (Q' : type686 A) (c : A -> Prop) : (term124 A u Q' c) = (term90 A u Q' c).
Proof. exact (eq_refl (term124 A u Q' c)). Qed.
Lemma lem4844887 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4844888 {A : Type'} (u : type686 A) (Q' : type686 A) (c : A -> Prop) : (term130 A u Q' c) = (term131 A u Q' c).
Proof. exact (MK_COMB (@lem4844887) (@lem4844886 A u Q' c)). Qed.
Lemma lem4844889 {A : Type'} (u : type686 A) (s : A -> Prop) : (term100 A u s) = (term100 A u s).
Proof. exact (eq_refl (term100 A u s)). Qed.
Lemma lem4844890 {A : Type'} (Q' : type686 A) (c : A -> Prop) (u : type686 A) (s : A -> Prop) : (term132 A Q' c u s) = (term133 A Q' c u s).
Proof. exact (MK_COMB (@lem4844888 A u Q' c) (@lem4844889 A u s)). Qed.
Lemma lem4844891 {A : Type'} (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term134 A Q' u s) = (term135 A Q' u s).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4844890 A Q' c u s)). Qed.
Lemma lem4844892 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4844893 {A : Type'} (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term123 A Q' u s) = (term136 A Q' u s).
Proof. exact (MK_COMB (@lem4844892 A) (@lem4844891 A Q' u s)). Qed.
Lemma lem4844894 {A : Type'} (Q' : type686 A) (u : type686 A) (s : A -> Prop) : ((term122 A Q' u s) = (term123 A Q' u s)) = ((term104 A Q' u s) = (term136 A Q' u s)).
Proof. exact (MK_COMB (@lem4844885 A Q' u s) (@lem4844893 A Q' u s)). Qed.
Lemma lem4844895 {A : Type'} (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term104 A Q' u s) = (term136 A Q' u s).
Proof. exact (EQ_MP (@lem4844894 A Q' u s) (@lem4844875 A Q' u s)). Qed.
Lemma lem4844896 {A : Type'} (P : type180 A) (u : type686 A) : (term106 A P u) = (term106 A P u).
Proof. exact (eq_refl (term106 A P u)). Qed.
Lemma lem4844897 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term108 A P Q' u s) = (term137 A P Q' u s).
Proof. exact (MK_COMB (@lem4844896 A P u) (@lem4844895 A Q' u s)). Qed.
Lemma lem4844899 {A : Type'} (P : Prop) (Q : A -> Prop) : (term138 A P Q) = (term139 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4844900 {A : Type'} (P : Prop) (Q : type686 A) : (term140 A P Q) = (term141 A P Q).
Proof. exact (@lem4844899 (A -> Prop) P Q). Qed.
Lemma lem4844901 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term142 A P Q' u s) = (term143 A P Q' u s).
Proof. exact (@lem4844900 A (term144 A P u) (term135 A Q' u s)). Qed.
Lemma lem4844902 {A : Type'} (Q' : type686 A) (c : A -> Prop) (u : type686 A) (s : A -> Prop) : (term145 A Q' u s c) = (term133 A Q' c u s).
Proof. exact (eq_refl (term145 A Q' u s c)). Qed.
Lemma lem4844903 {A : Type'} (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term146 A Q' u s) = (term135 A Q' u s).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4844902 A Q' c u s)). Qed.
Lemma lem4844904 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4844905 {A : Type'} (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term147 A Q' u s) = (term136 A Q' u s).
Proof. exact (MK_COMB (@lem4844904 A) (@lem4844903 A Q' u s)). Qed.
Lemma lem4844906 {A : Type'} (P : type180 A) (u : type686 A) : (term106 A P u) = (term106 A P u).
Proof. exact (eq_refl (term106 A P u)). Qed.
Lemma lem4844907 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term142 A P Q' u s) = (term137 A P Q' u s).
Proof. exact (MK_COMB (@lem4844906 A P u) (@lem4844905 A Q' u s)). Qed.
Lemma lem4844908 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4844909 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term148 A P Q' u s) = (term149 A P Q' u s).
Proof. exact (MK_COMB (@lem4844908) (@lem4844907 A P Q' u s)). Qed.
Lemma lem4844910 {A : Type'} (Q' : type686 A) (c : A -> Prop) (u : type686 A) (s : A -> Prop) : (term145 A Q' u s c) = (term133 A Q' c u s).
Proof. exact (eq_refl (term145 A Q' u s c)). Qed.
Lemma lem4844911 {A : Type'} (P : type180 A) (u : type686 A) : (term106 A P u) = (term106 A P u).
Proof. exact (eq_refl (term106 A P u)). Qed.
Lemma lem4844912 {A : Type'} (P : type180 A) (Q' : type686 A) (c : A -> Prop) (u : type686 A) (s : A -> Prop) : (term150 A P Q' u s c) = (term151 A P Q' c u s).
Proof. exact (MK_COMB (@lem4844911 A P u) (@lem4844910 A Q' c u s)). Qed.
Lemma lem4844913 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term152 A P Q' u s) = (term153 A P Q' u s).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4844912 A P Q' c u s)). Qed.
Lemma lem4844914 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4844915 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term143 A P Q' u s) = (term154 A P Q' u s).
Proof. exact (MK_COMB (@lem4844914 A) (@lem4844913 A P Q' u s)). Qed.
Lemma lem4844916 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : ((term142 A P Q' u s) = (term143 A P Q' u s)) = ((term137 A P Q' u s) = (term154 A P Q' u s)).
Proof. exact (MK_COMB (@lem4844909 A P Q' u s) (@lem4844915 A P Q' u s)). Qed.
Lemma lem4844917 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term137 A P Q' u s) = (term154 A P Q' u s).
Proof. exact (EQ_MP (@lem4844916 A P Q' u s) (@lem4844901 A P Q' u s)). Qed.
Lemma lem4844918 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term108 A P Q' u s) = (term154 A P Q' u s).
Proof. exact (TRANS (@lem4844897 A P Q' u s) (@lem4844917 A P Q' u s)). Qed.
Lemma lem4844919 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term116 A P Q' s) = (term155 A P Q' s).
Proof. exact (fun_ext (fun u : type686 A => @lem4844918 A P Q' u s)). Qed.
Lemma lem4844920 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4844921 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term117 A P Q' s) = (term156 A P Q' s).
Proof. exact (MK_COMB (@lem4844920 A) (@lem4844919 A P Q' s)). Qed.
Lemma lem4844923 {A B : Type'} (P : type1413 A B) : (term157 A B P) = (term158 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4844924 {A : Type'} (P : type174 A) : (term159 A P) = (term160 A P).
Proof. exact (@lem4844923 (type686 A) (A -> Prop) P). Qed.
Lemma lem4844925 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term161 A P Q' s) = (term162 A P Q' s).
Proof. exact (@lem4844924 A (term163 A P Q' s)). Qed.
Lemma lem4844926 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term164 A P Q' s u) = (term153 A P Q' u s).
Proof. exact (eq_refl (term164 A P Q' s u)). Qed.
Lemma lem4844927 {A : Type'} (c : A -> Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem4844928 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) (c : A -> Prop) : (term165 A P Q' s u c) = (term166 A P Q' u s c).
Proof. exact (MK_COMB (@lem4844926 A P Q' u s) (@lem4844927 A c)). Qed.
Lemma lem4844929 {A : Type'} (P : type180 A) (Q' : type686 A) (c : A -> Prop) (u : type686 A) (s : A -> Prop) : (term166 A P Q' u s c) = (term151 A P Q' c u s).
Proof. exact (eq_refl (term166 A P Q' u s c)). Qed.
Lemma lem4844930 {A : Type'} (P : type180 A) (Q' : type686 A) (c : A -> Prop) (u : type686 A) (s : A -> Prop) : (term165 A P Q' s u c) = (term151 A P Q' c u s).
Proof. exact (TRANS (@lem4844928 A P Q' u s c) (@lem4844929 A P Q' c u s)). Qed.
Lemma lem4844931 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term167 A P Q' s u) = (term153 A P Q' u s).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4844930 A P Q' c u s)). Qed.
Lemma lem4844932 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4844933 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term168 A P Q' s u) = (term154 A P Q' u s).
Proof. exact (MK_COMB (@lem4844932 A) (@lem4844931 A P Q' u s)). Qed.
Lemma lem4844934 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term169 A P Q' s) = (term155 A P Q' s).
Proof. exact (fun_ext (fun u : type686 A => @lem4844933 A P Q' u s)). Qed.
Lemma lem4844935 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4844936 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term161 A P Q' s) = (term156 A P Q' s).
Proof. exact (MK_COMB (@lem4844935 A) (@lem4844934 A P Q' s)). Qed.
Lemma lem4844937 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4844938 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term170 A P Q' s) = (term171 A P Q' s).
Proof. exact (MK_COMB (@lem4844937) (@lem4844936 A P Q' s)). Qed.
Lemma lem4844939 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term164 A P Q' s u) = (term153 A P Q' u s).
Proof. exact (eq_refl (term164 A P Q' s u)). Qed.
Lemma lem4844940 {A : Type'} (c : type178 A) (u : type686 A) : (c u) = (c u).
Proof. exact (eq_refl (c u)). Qed.
Lemma lem4844941 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) (c : type178 A) (u : type686 A) : (term172 A P Q' s c u) = (term173 A P Q' s c u).
Proof. exact (MK_COMB (@lem4844939 A P Q' u s) (@lem4844940 A c u)). Qed.
Lemma lem4844942 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (u : type686 A) (s : A -> Prop) : (term173 A P Q' s c u) = (term174 A P Q' c u s).
Proof. exact (eq_refl (term173 A P Q' s c u)). Qed.
Lemma lem4844943 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (u : type686 A) (s : A -> Prop) : (term172 A P Q' s c u) = (term174 A P Q' c u s).
Proof. exact (TRANS (@lem4844941 A P Q' s c u) (@lem4844942 A P Q' c u s)). Qed.
Lemma lem4844944 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (s : A -> Prop) : (term175 A P Q' s c) = (term176 A P Q' c s).
Proof. exact (fun_ext (fun u : type686 A => @lem4844943 A P Q' c u s)). Qed.
Lemma lem4844945 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4844946 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (s : A -> Prop) : (term177 A P Q' s c) = (term178 A P Q' c s).
Proof. exact (MK_COMB (@lem4844945 A) (@lem4844944 A P Q' c s)). Qed.
Lemma lem4844947 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term179 A P Q' s) = (term180 A P Q' s).
Proof. exact (fun_ext (fun c : type178 A => @lem4844946 A P Q' c s)). Qed.
Lemma lem4844948 {A : Type'} : (@ex (((A -> Prop) -> Prop) -> A -> Prop)) = (@ex (((A -> Prop) -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex (((A -> Prop) -> Prop) -> A -> Prop))). Qed.
Lemma lem4844949 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term162 A P Q' s) = (term181 A P Q' s).
Proof. exact (MK_COMB (@lem4844948 A) (@lem4844947 A P Q' s)). Qed.
Lemma lem4844950 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : ((term161 A P Q' s) = (term162 A P Q' s)) = ((term156 A P Q' s) = (term181 A P Q' s)).
Proof. exact (MK_COMB (@lem4844938 A P Q' s) (@lem4844949 A P Q' s)). Qed.
Lemma lem4844951 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term156 A P Q' s) = (term181 A P Q' s).
Proof. exact (EQ_MP (@lem4844950 A P Q' s) (@lem4844925 A P Q' s)). Qed.
Lemma lem4844953 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term117 A P Q' s) = (term181 A P Q' s).
Proof. exact (TRANS (@lem4844921 A P Q' s) (@lem4844951 A P Q' s)). Qed.
Lemma lem4844954 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term56 A P Q' s) = (term181 A P Q' s).
Proof. exact (TRANS (@lem4844774 A P Q' s) (@lem4844953 A P Q' s)). Qed.
Lemma lem4844955 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) (h1 : term56 A P Q' s) : term181 A P Q' s.
Proof. exact (EQ_MP (@lem4844954 A P Q' s) (@lem4844581 A P Q' s h1)). Qed.
Lemma lem4844956 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (s : A -> Prop) (h1 : term178 A P Q' c s) : term178 A P Q' c s.
Proof. exact (h1). Qed.
Lemma lem4844957 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term85 A P u s Q Q'.
Proof. exact (h1). Qed.
Lemma lem4844994 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (u : type686 A) (s : A -> Prop) : (term174 A P Q' c u s) = (term174 A P Q' c u s).
Proof. exact (eq_refl (term174 A P Q' c u s)). Qed.
Lemma lem4844995 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (s : A -> Prop) : (term176 A P Q' c s) = (term176 A P Q' c s).
Proof. exact (fun_ext (fun u : type686 A => @lem4844994 A P Q' c u s)). Qed.
Lemma lem4844996 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4844997 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (s : A -> Prop) : (term178 A P Q' c s) = (term178 A P Q' c s).
Proof. exact (MK_COMB (@lem4844996 A) (@lem4844995 A P Q' c s)). Qed.
Lemma lem4844998 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (s : A -> Prop) (h1 : term178 A P Q' c s) : term178 A P Q' c s.
Proof. exact (EQ_MP (@lem4844997 A P Q' c s) (@lem4844956 A P Q' c s h1)). Qed.
Lemma lem4845009 {A : Type'} (Q : type686 A) (Q' : type686 A) (x : A -> Prop) : (term65 A Q Q' x) = (term65 A Q Q' x).
Proof. exact (eq_refl (term65 A Q Q' x)). Qed.
Lemma lem4845010 {A : Type'} (Q : type686 A) (Q' : type686 A) : (term66 A Q Q') = (term66 A Q Q').
Proof. exact (fun_ext (fun x : A -> Prop => @lem4845009 A Q Q' x)). Qed.
Lemma lem4845011 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4845012 {A : Type'} (Q : type686 A) (Q' : type686 A) : (term67 A Q Q') = (term67 A Q Q').
Proof. exact (MK_COMB (@lem4845011 A) (@lem4845010 A Q Q')). Qed.
Lemma lem4845019 {A : Type'} (u : type686 A) (s : A -> Prop) : ((@INTERS A u) = s) = ((@INTERS A u) = s).
Proof. exact (eq_refl ((@INTERS A u) = s)). Qed.
Lemma lem4845032 {A : Type'} (u : type686 A) (Q : type686 A) (c : A -> Prop) : (term57 A u Q c) = (term57 A u Q c).
Proof. exact (eq_refl (term57 A u Q c)). Qed.
Lemma lem4845033 {A : Type'} (u : type686 A) (Q : type686 A) : (term58 A u Q) = (term58 A u Q).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4845032 A u Q c)). Qed.
Lemma lem4845034 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4845035 {A : Type'} (u : type686 A) (Q : type686 A) : (term59 A u Q) = (term59 A u Q).
Proof. exact (MK_COMB (@lem4845034 A) (@lem4845033 A u Q)). Qed.
Lemma lem4845036 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4845037 {A : Type'} (u : type686 A) (Q : type686 A) : (term60 A u Q) = (term60 A u Q).
Proof. exact (MK_COMB (@lem4845036) (@lem4845035 A u Q)). Qed.
Lemma lem4845038 {A : Type'} (Q : type686 A) (u : type686 A) (s : A -> Prop) : (term61 A Q u s) = (term61 A Q u s).
Proof. exact (MK_COMB (@lem4845037 A u Q) (@lem4845019 A u s)). Qed.
Lemma lem4845043 {A : Type'} (P : type180 A) (u : type686 A) : (term50 A P u) = (term50 A P u).
Proof. exact (eq_refl (term50 A P u)). Qed.
Lemma lem4845044 {A : Type'} (P : type180 A) (Q : type686 A) (u : type686 A) (s : A -> Prop) : (term62 A P Q u s) = (term62 A P Q u s).
Proof. exact (MK_COMB (@lem4845043 A P u) (@lem4845038 A Q u s)). Qed.
Lemma lem4845045 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4845046 {A : Type'} (P : type180 A) (Q : type686 A) (u : type686 A) (s : A -> Prop) : (term83 A P Q u s) = (term83 A P Q u s).
Proof. exact (MK_COMB (@lem4845045) (@lem4845044 A P Q u s)). Qed.
Lemma lem4845047 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) : (term85 A P u s Q Q') = (term85 A P u s Q Q').
Proof. exact (MK_COMB (@lem4845046 A P Q u s) (@lem4845012 A Q Q')). Qed.
Lemma lem4845048 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term85 A P u s Q Q'.
Proof. exact (EQ_MP (@lem4845047 A P u s Q Q') (@lem4844957 A P u s Q Q' h1)). Qed.
Lemma lem4845049 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term67 A Q Q'.
Proof. exact (proj2 (@lem4845048 A P u s Q Q' h1)). Qed.
Lemma lem4845050 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term62 A P Q u s.
Proof. exact (proj1 (@lem4845048 A P u s Q Q' h1)). Qed.
Lemma lem4845051 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term61 A Q u s.
Proof. exact (proj2 (@lem4845050 A P u s Q Q' h1)). Qed.
Lemma lem4845054 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term59 A u Q.
Proof. exact (proj1 (@lem4845051 A P u s Q Q' h1)). Qed.
Lemma lem4845072 {A : Type'} (Q' : type686 A) (c : type178 A) (u : type686 A) (s : A -> Prop) : (term182 A Q' c u s) = (term183 A Q' c u s).
Proof. exact (@lem19699 (term184 A c u) (term185 A Q' c u) (term100 A u s)). Qed.
Lemma lem4845075 {A : Type'} (P : type180 A) (u : type686 A) : (term106 A P u) = (term106 A P u).
Proof. exact (eq_refl (term106 A P u)). Qed.
Lemma lem4845076 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (u : type686 A) (s : A -> Prop) : (term174 A P Q' c u s) = (term186 A P Q' c u s).
Proof. exact (MK_COMB (@lem4845075 A P u) (@lem4845072 A Q' c u s)). Qed.
Lemma lem4845083 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (u : type686 A) (s : A -> Prop) : (term186 A P Q' c u s) = (term187 A P Q' c u s).
Proof. exact (@lem19490 (term188 A c u s) (term144 A P u) (term189 A Q' c u s)). Qed.
Lemma lem4845084 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (u : type686 A) (s : A -> Prop) : (term174 A P Q' c u s) = (term187 A P Q' c u s).
Proof. exact (TRANS (@lem4845076 A P Q' c u s) (@lem4845083 A P Q' c u s)). Qed.
Lemma lem4845085 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (s : A -> Prop) : (term176 A P Q' c s) = (term190 A P Q' c s).
Proof. exact (fun_ext (fun u : type686 A => @lem4845084 A P Q' c u s)). Qed.
Lemma lem4845086 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4845088 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (s : A -> Prop) : (term178 A P Q' c s) = (term191 A P Q' c s).
Proof. exact (MK_COMB (@lem4845086 A) (@lem4845085 A P Q' c s)). Qed.
Lemma lem4845089 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (s : A -> Prop) (h1 : term178 A P Q' c s) : term191 A P Q' c s.
Proof. exact (EQ_MP (@lem4845088 A P Q' c s) (@lem4844998 A P Q' c s h1)). Qed.
Lemma lem4845097 {A : Type'} (Q : type686 A) (Q' : type686 A) (x : A -> Prop) : (term65 A Q Q' x) = (term65 A Q Q' x).
Proof. exact (eq_refl (term65 A Q Q' x)). Qed.
Lemma lem4845098 {A : Type'} (Q : type686 A) (Q' : type686 A) : (term66 A Q Q') = (term66 A Q Q').
Proof. exact (fun_ext (fun x : A -> Prop => @lem4845097 A Q Q' x)). Qed.
Lemma lem4845099 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4845101 {A : Type'} (Q : type686 A) (Q' : type686 A) : (term67 A Q Q') = (term67 A Q Q').
Proof. exact (MK_COMB (@lem4845099 A) (@lem4845098 A Q Q')). Qed.
Lemma lem4845102 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term67 A Q Q'.
Proof. exact (EQ_MP (@lem4845101 A Q Q') (@lem4845049 A P u s Q Q' h1)). Qed.
Lemma lem4845114 {A : Type'} (u : type686 A) (Q : type686 A) (c : A -> Prop) : (term57 A u Q c) = (term57 A u Q c).
Proof. exact (eq_refl (term57 A u Q c)). Qed.
Lemma lem4845115 {A : Type'} (u : type686 A) (Q : type686 A) : (term58 A u Q) = (term58 A u Q).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4845114 A u Q c)). Qed.
Lemma lem4845116 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4845118 {A : Type'} (u : type686 A) (Q : type686 A) : (term59 A u Q) = (term59 A u Q).
Proof. exact (MK_COMB (@lem4845116 A) (@lem4845115 A u Q)). Qed.
Lemma lem4845119 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term59 A u Q.
Proof. exact (EQ_MP (@lem4845118 A u Q) (@lem4845054 A P u s Q Q' h1)). Qed.
Lemma lem4845124 {A : Type'} (_60085 : type686 A) (P : type180 A) (Q' : type686 A) (c : type178 A) (s : A -> Prop) (h1 : term178 A P Q' c s) : term192 A P Q' c s _60085.
Proof. exact (@lem4845089 A P Q' c s h1 _60085). Qed.
Lemma lem4845125 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (_60085 : type686 A) (s : A -> Prop) : (term192 A P Q' c s _60085) = (term187 A P Q' c _60085 s).
Proof. exact (eq_refl (term192 A P Q' c s _60085)). Qed.
Lemma lem4845126 {A : Type'} (_60085 : type686 A) (P : type180 A) (Q' : type686 A) (c : type178 A) (s : A -> Prop) (h1 : term178 A P Q' c s) : term187 A P Q' c _60085 s.
Proof. exact (EQ_MP (@lem4845125 A P Q' c _60085 s) (@lem4845124 A _60085 P Q' c s h1)). Qed.
Lemma lem4845127 {A : Type'} (_60086 : A -> Prop) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term193 A Q Q' _60086.
Proof. exact (@lem4845102 A P u s Q Q' h1 _60086). Qed.
Lemma lem4845128 {A : Type'} (Q : type686 A) (Q' : type686 A) (_60086 : A -> Prop) : (term193 A Q Q' _60086) = (term65 A Q Q' _60086).
Proof. exact (eq_refl (term193 A Q Q' _60086)). Qed.
Lemma lem4845130 {A : Type'} (_60087 : A -> Prop) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term194 A u Q _60087.
Proof. exact (@lem4845119 A P u s Q Q' h1 _60087). Qed.
Lemma lem4845131 {A : Type'} (u : type686 A) (Q : type686 A) (_60087 : A -> Prop) : (term194 A u Q _60087) = (term57 A u Q _60087).
Proof. exact (eq_refl (term194 A u Q _60087)). Qed.
Lemma lem4845150 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : (@INTERS A u) = s.
Proof. exact (proj2 (@lem4845051 A P u s Q Q' h1)). Qed.
Lemma lem4845160 {A : Type'} (_60085 : type686 A) (P : type180 A) (Q' : type686 A) (c : type178 A) (s : A -> Prop) (h1 : term178 A P Q' c s) : term195 A P c _60085 s.
Proof. exact (proj1 (@lem4845126 A _60085 P Q' c s h1)). Qed.
Lemma lem4845170 {A : Type'} (_60085 : type686 A) (P : type180 A) (Q' : type686 A) (c : type178 A) (s : A -> Prop) (h1 : term178 A P Q' c s) : term196 A P Q' c _60085 s.
Proof. exact (proj2 (@lem4845126 A _60085 P Q' c s h1)). Qed.
Lemma lem4845171 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : s = (@INTERS A u).
Proof. exact (SYM (@lem4845150 A P u s Q Q' h1)). Qed.
Lemma lem4845199 {A : Type'} (_60086 : A -> Prop) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term65 A Q Q' _60086.
Proof. exact (EQ_MP (@lem4845128 A Q Q' _60086) (@lem4845127 A _60086 P u s Q Q' h1)). Qed.
Lemma lem4845227 {A : Type'} (_60087 : A -> Prop) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term57 A u Q _60087.
Proof. exact (EQ_MP (@lem4845131 A u Q _60087) (@lem4845130 A _60087 P u s Q Q' h1)). Qed.
Lemma lem4845228 {A : Type'} (P : type180 A) (c : type178 A) (_60085 : type686 A) : (term197 A P c _60085) = (term197 A P c _60085).
Proof. exact (eq_refl (term197 A P c _60085)). Qed.
Lemma lem4845229 {A : Type'} (c : type178 A) (_60085 : type686 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : (term198 A P c _60085 s) = (term199 A P c _60085 u).
Proof. exact (MK_COMB (@lem4845228 A P c _60085) (@lem4845171 A P u s Q Q' h1)). Qed.
Lemma lem4845230 {A : Type'} (P : type180 A) (c : type178 A) (_60085 : type686 A) (u : type686 A) : (term199 A P c _60085 u) = (term200 A P c _60085 u).
Proof. exact (eq_refl (term199 A P c _60085 u)). Qed.
Lemma lem4845231 {A : Type'} (P : type180 A) (c : type178 A) (_60085 : type686 A) (s : A -> Prop) : (term201 A P c _60085 s) = (term201 A P c _60085 s).
Proof. exact (eq_refl (term201 A P c _60085 s)). Qed.
Lemma lem4845232 {A : Type'} (s : A -> Prop) (P : type180 A) (c : type178 A) (_60085 : type686 A) (u : type686 A) : ((term198 A P c _60085 s) = (term199 A P c _60085 u)) = ((term198 A P c _60085 s) = (term200 A P c _60085 u)).
Proof. exact (MK_COMB (@lem4845231 A P c _60085 s) (@lem4845230 A P c _60085 u)). Qed.
Lemma lem4845233 {A : Type'} (P : type180 A) (c : type178 A) (_60085 : type686 A) (s : A -> Prop) : (term198 A P c _60085 s) = (term195 A P c _60085 s).
Proof. exact (eq_refl (term198 A P c _60085 s)). Qed.
Lemma lem4845234 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4845235 {A : Type'} (P : type180 A) (c : type178 A) (_60085 : type686 A) (s : A -> Prop) : (term201 A P c _60085 s) = (term202 A P c _60085 s).
Proof. exact (MK_COMB (@lem4845234) (@lem4845233 A P c _60085 s)). Qed.
Lemma lem4845236 {A : Type'} (P : type180 A) (c : type178 A) (_60085 : type686 A) (u : type686 A) : (term200 A P c _60085 u) = (term200 A P c _60085 u).
Proof. exact (eq_refl (term200 A P c _60085 u)). Qed.
Lemma lem4845237 {A : Type'} (s : A -> Prop) (P : type180 A) (c : type178 A) (_60085 : type686 A) (u : type686 A) : ((term198 A P c _60085 s) = (term200 A P c _60085 u)) = ((term195 A P c _60085 s) = (term200 A P c _60085 u)).
Proof. exact (MK_COMB (@lem4845235 A P c _60085 s) (@lem4845236 A P c _60085 u)). Qed.
Lemma lem4845238 {A : Type'} (s : A -> Prop) (P : type180 A) (c : type178 A) (_60085 : type686 A) (u : type686 A) : ((term198 A P c _60085 s) = (term199 A P c _60085 u)) = ((term195 A P c _60085 s) = (term200 A P c _60085 u)).
Proof. exact (TRANS (@lem4845232 A s P c _60085 u) (@lem4845237 A s P c _60085 u)). Qed.
Lemma lem4845239 {A : Type'} (c : type178 A) (_60085 : type686 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : (term195 A P c _60085 s) = (term200 A P c _60085 u).
Proof. exact (EQ_MP (@lem4845238 A s P c _60085 u) (@lem4845229 A c _60085 P u s Q Q' h1)). Qed.
Lemma lem4845240 {A : Type'} (_60085 : type686 A) (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term200 A P c _60085 u.
Proof. exact (EQ_MP (@lem4845239 A c _60085 P u s Q Q' h2) (@lem4845160 A _60085 P Q' c s h1)). Qed.
Lemma lem4845241 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (_60085 : type686 A) : (term203 A P Q' c _60085) = (term203 A P Q' c _60085).
Proof. exact (eq_refl (term203 A P Q' c _60085)). Qed.
Lemma lem4845242 {A : Type'} (c : type178 A) (_60085 : type686 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : (term204 A P Q' c _60085 s) = (term205 A P Q' c _60085 u).
Proof. exact (MK_COMB (@lem4845241 A P Q' c _60085) (@lem4845171 A P u s Q Q' h1)). Qed.
Lemma lem4845243 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (_60085 : type686 A) (u : type686 A) : (term205 A P Q' c _60085 u) = (term206 A P Q' c _60085 u).
Proof. exact (eq_refl (term205 A P Q' c _60085 u)). Qed.
Lemma lem4845244 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (_60085 : type686 A) (s : A -> Prop) : (term207 A P Q' c _60085 s) = (term207 A P Q' c _60085 s).
Proof. exact (eq_refl (term207 A P Q' c _60085 s)). Qed.
Lemma lem4845245 {A : Type'} (s : A -> Prop) (P : type180 A) (Q' : type686 A) (c : type178 A) (_60085 : type686 A) (u : type686 A) : ((term204 A P Q' c _60085 s) = (term205 A P Q' c _60085 u)) = ((term204 A P Q' c _60085 s) = (term206 A P Q' c _60085 u)).
Proof. exact (MK_COMB (@lem4845244 A P Q' c _60085 s) (@lem4845243 A P Q' c _60085 u)). Qed.
Lemma lem4845246 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (_60085 : type686 A) (s : A -> Prop) : (term204 A P Q' c _60085 s) = (term196 A P Q' c _60085 s).
Proof. exact (eq_refl (term204 A P Q' c _60085 s)). Qed.
Lemma lem4845247 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4845248 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (_60085 : type686 A) (s : A -> Prop) : (term207 A P Q' c _60085 s) = (term208 A P Q' c _60085 s).
Proof. exact (MK_COMB (@lem4845247) (@lem4845246 A P Q' c _60085 s)). Qed.
Lemma lem4845249 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (_60085 : type686 A) (u : type686 A) : (term206 A P Q' c _60085 u) = (term206 A P Q' c _60085 u).
Proof. exact (eq_refl (term206 A P Q' c _60085 u)). Qed.
Lemma lem4845250 {A : Type'} (s : A -> Prop) (P : type180 A) (Q' : type686 A) (c : type178 A) (_60085 : type686 A) (u : type686 A) : ((term204 A P Q' c _60085 s) = (term206 A P Q' c _60085 u)) = ((term196 A P Q' c _60085 s) = (term206 A P Q' c _60085 u)).
Proof. exact (MK_COMB (@lem4845248 A P Q' c _60085 s) (@lem4845249 A P Q' c _60085 u)). Qed.
Lemma lem4845251 {A : Type'} (s : A -> Prop) (P : type180 A) (Q' : type686 A) (c : type178 A) (_60085 : type686 A) (u : type686 A) : ((term204 A P Q' c _60085 s) = (term205 A P Q' c _60085 u)) = ((term196 A P Q' c _60085 s) = (term206 A P Q' c _60085 u)).
Proof. exact (TRANS (@lem4845245 A s P Q' c _60085 u) (@lem4845250 A s P Q' c _60085 u)). Qed.
Lemma lem4845252 {A : Type'} (c : type178 A) (_60085 : type686 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : (term196 A P Q' c _60085 s) = (term206 A P Q' c _60085 u).
Proof. exact (EQ_MP (@lem4845251 A s P Q' c _60085 u) (@lem4845242 A c _60085 P u s Q Q' h1)). Qed.
Lemma lem4845253 {A : Type'} (_60085 : type686 A) (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term206 A P Q' c _60085 u.
Proof. exact (EQ_MP (@lem4845252 A c _60085 P u s Q Q' h2) (@lem4845170 A _60085 P Q' c s h1)). Qed.
Lemma lem4845330 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : P u.
Proof. exact (proj1 (@lem4845050 A P u s Q Q' h1)). Qed.
Lemma lem4845331 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term209 A P u.
Proof. exact (fun h0 : term144 A P u => @lem4845330 A P u s Q Q' h1). Qed.
Lemma lem4845333 (p : Prop) : (term210 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4845334 {A : Type'} (P : type180 A) (u : type686 A) : (term209 A P u) = (P u).
Proof. exact (@lem4845333 (P u)). Qed.
Lemma lem4845335 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : P u.
Proof. exact (EQ_MP (@lem4845334 A P u) (@lem4845331 A P u s Q Q' h1)). Qed.
Lemma lem4845337 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : P u.
Proof. exact (proj1 (@lem4845050 A P u s Q Q' h1)). Qed.
Lemma lem4845338 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term209 A P u.
Proof. exact (fun h0 : term144 A P u => @lem4845337 A P u s Q Q' h1). Qed.
Lemma lem4845340 (p : Prop) : (term210 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4845341 {A : Type'} (P : type180 A) (u : type686 A) : (term209 A P u) = (P u).
Proof. exact (@lem4845340 (P u)). Qed.
Lemma lem4845342 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : P u.
Proof. exact (EQ_MP (@lem4845341 A P u) (@lem4845338 A P u s Q Q' h1)). Qed.
Lemma lem4845344 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem21386 (A -> Prop) x). Qed.
Lemma lem4845345 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem4845344 A x). Qed.
Lemma lem4845346 {A : Type'} (u : type686 A) : (@INTERS A u) = (@INTERS A u).
Proof. exact (@lem4845345 A (@INTERS A u)). Qed.
Lemma lem4845347 {A : Type'} (u : type686 A) : term211 A u.
Proof. exact (fun h0 : term212 A u => @lem4845346 A u). Qed.
Lemma lem4845349 (p : Prop) : (term210 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4845350 {A : Type'} (u : type686 A) : (term211 A u) = ((@INTERS A u) = (@INTERS A u)).
Proof. exact (@lem4845349 ((@INTERS A u) = (@INTERS A u))). Qed.
Lemma lem4845351 {A : Type'} (u : type686 A) : (@INTERS A u) = (@INTERS A u).
Proof. exact (EQ_MP (@lem4845350 A u) (@lem4845347 A u)). Qed.
Lemma lem4845357 (q : Prop) (p : Prop) (r : Prop) : (term213 p q r) = (term213 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4845358 {A : Type'} (c : type178 A) (P : type180 A) (_60085 : type686 A) (u : type686 A) : (term200 A P c _60085 u) = (term214 A c P _60085 u).
Proof. exact (@lem4845357 (term184 A c _60085) (term144 A P _60085) (term215 A _60085 u)). Qed.
Lemma lem4845376 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4845377 {A : Type'} (c : type178 A) (P : type180 A) (_60085 : type686 A) (u : type686 A) : (term216 A P c _60085 u) = (term217 A c P _60085 u).
Proof. exact (MK_COMB (@lem4845376) (@lem4845358 A c P _60085 u)). Qed.
Lemma lem4845395 {A : Type'} (c : type178 A) (P : type180 A) (_60085 : type686 A) (u : type686 A) : (term214 A c P _60085 u) = (term214 A c P _60085 u).
Proof. exact (eq_refl (term214 A c P _60085 u)). Qed.
Lemma lem4845396 {A : Type'} (c : type178 A) (P : type180 A) (_60085 : type686 A) (u : type686 A) : ((term200 A P c _60085 u) = (term214 A c P _60085 u)) = ((term214 A c P _60085 u) = (term214 A c P _60085 u)).
Proof. exact (MK_COMB (@lem4845377 A c P _60085 u) (@lem4845395 A c P _60085 u)). Qed.
Lemma lem4845398 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4845399 (x : Prop) : (x = x) = True.
Proof. exact (@lem4845398 Prop x). Qed.
Lemma lem4845400 {A : Type'} (c : type178 A) (P : type180 A) (_60085 : type686 A) (u : type686 A) : ((term214 A c P _60085 u) = (term214 A c P _60085 u)) = True.
Proof. exact (@lem4845399 (term214 A c P _60085 u)). Qed.
Lemma lem4845401 {A : Type'} (c : type178 A) (P : type180 A) (_60085 : type686 A) (u : type686 A) : ((term200 A P c _60085 u) = (term214 A c P _60085 u)) = True.
Proof. exact (TRANS (@lem4845396 A c P _60085 u) (@lem4845400 A c P _60085 u)). Qed.
Lemma lem4845402 {A : Type'} (c : type178 A) (P : type180 A) (_60085 : type686 A) (u : type686 A) : True = ((term200 A P c _60085 u) = (term214 A c P _60085 u)).
Proof. exact (SYM (@lem4845401 A c P _60085 u)). Qed.
Lemma lem4845403 {A : Type'} (c : type178 A) (P : type180 A) (_60085 : type686 A) (u : type686 A) : (term200 A P c _60085 u) = (term214 A c P _60085 u).
Proof. exact (EQ_MP (@lem4845402 A c P _60085 u) (@lem0)). Qed.
Lemma lem4845404 {A : Type'} (_60085 : type686 A) (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term214 A c P _60085 u.
Proof. exact (EQ_MP (@lem4845403 A c P _60085 u) (@lem4845240 A _60085 c P u s Q Q' h1 h2)). Qed.
Lemma lem4845406 (b : Prop) (a : Prop) : (a \/ b) = (term218 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4845407 {A : Type'} (P : type180 A) (u : type686 A) (c : type178 A) (_60085 : type686 A) : (term214 A c P _60085 u) = (term219 A P u c _60085).
Proof. exact (@lem4845406 (term220 A P _60085 u) (term184 A c _60085)). Qed.
Lemma lem4845409 (a : Prop) (b : Prop) : (term221 a b) = (term222 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4845410 {A : Type'} (P : type180 A) (_60085 : type686 A) (u : type686 A) : (term223 A P _60085 u) = (term224 A P _60085 u).
Proof. exact (@lem4845409 (term144 A P _60085) (term215 A _60085 u)). Qed.
Lemma lem4845412 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4845413 {A : Type'} (P : type180 A) (_60085 : type686 A) : (term225 A P _60085) = (P _60085).
Proof. exact (@lem4845412 (P _60085)). Qed.
Lemma lem4845414 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4845415 {A : Type'} (P : type180 A) (_60085 : type686 A) : (term226 A P _60085) = (term50 A P _60085).
Proof. exact (MK_COMB (@lem4845414) (@lem4845413 A P _60085)). Qed.
Lemma lem4845417 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4845418 {A : Type'} (_60085 : type686 A) (u : type686 A) : (term227 A _60085 u) = ((@INTERS A _60085) = (@INTERS A u)).
Proof. exact (@lem4845417 ((@INTERS A _60085) = (@INTERS A u))). Qed.
Lemma lem4845419 {A : Type'} (P : type180 A) (_60085 : type686 A) (u : type686 A) : (term224 A P _60085 u) = (term228 A P _60085 u).
Proof. exact (MK_COMB (@lem4845415 A P _60085) (@lem4845418 A _60085 u)). Qed.
Lemma lem4845420 {A : Type'} (P : type180 A) (_60085 : type686 A) (u : type686 A) : (term223 A P _60085 u) = (term228 A P _60085 u).
Proof. exact (TRANS (@lem4845410 A P _60085 u) (@lem4845419 A P _60085 u)). Qed.
Lemma lem4845421 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4845422 {A : Type'} (P : type180 A) (_60085 : type686 A) (u : type686 A) : (term229 A P _60085 u) = (term230 A P _60085 u).
Proof. exact (MK_COMB (@lem4845421) (@lem4845420 A P _60085 u)). Qed.
Lemma lem4845423 {A : Type'} (c : type178 A) (_60085 : type686 A) : (term184 A c _60085) = (term184 A c _60085).
Proof. exact (eq_refl (term184 A c _60085)). Qed.
Lemma lem4845424 {A : Type'} (P : type180 A) (u : type686 A) (c : type178 A) (_60085 : type686 A) : (term219 A P u c _60085) = (term231 A P u c _60085).
Proof. exact (MK_COMB (@lem4845422 A P _60085 u) (@lem4845423 A c _60085)). Qed.
Lemma lem4845425 {A : Type'} (P : type180 A) (u : type686 A) (c : type178 A) (_60085 : type686 A) : (term214 A c P _60085 u) = (term231 A P u c _60085).
Proof. exact (TRANS (@lem4845407 A P u c _60085) (@lem4845424 A P u c _60085)). Qed.
Lemma lem4845427 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term232 A P u.
Proof. exact (conj (@lem4845342 A P u s Q Q' h1) (@lem4845351 A u)). Qed.
Lemma lem4845429 {A : Type'} (_60085 : type686 A) (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term231 A P u c _60085.
Proof. exact (EQ_MP (@lem4845425 A P u c _60085) (@lem4845404 A _60085 c P u s Q Q' h1 h2)). Qed.
Lemma lem4845430 {A : Type'} (_60085 : type686 A) (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term231 A P u c _60085.
Proof. exact (@lem4845429 A _60085 c P u s Q Q' h1 h2). Qed.
Lemma lem4845431 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term233 A P c u.
Proof. exact (@lem4845430 A u c P u s Q Q' h1 h2). Qed.
Lemma lem4845434 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term184 A c u.
Proof. exact (@lem4845431 A c P u s Q Q' h1 h2 (@lem4845427 A P u s Q Q' h2)). Qed.
Lemma lem4845435 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term234 A c u.
Proof. exact (fun h0 : term235 A c u => @lem4845434 A c P u s Q Q' h1 h2). Qed.
Lemma lem4845437 (p : Prop) : (term210 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4845438 {A : Type'} (c : type178 A) (u : type686 A) : (term234 A c u) = (term184 A c u).
Proof. exact (@lem4845437 (term184 A c u)). Qed.
Lemma lem4845439 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term184 A c u.
Proof. exact (EQ_MP (@lem4845438 A c u) (@lem4845435 A c P u s Q Q' h1 h2)). Qed.
Lemma lem4845445 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4845446 {A : Type'} (Q : type686 A) (_60087 : A -> Prop) (u : type686 A) : (term57 A u Q _60087) = (term236 A Q _60087 u).
Proof. exact (@lem4845445 (Q _60087) (term237 A _60087 u)). Qed.
Lemma lem4845452 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4845453 {A : Type'} (Q : type686 A) (_60087 : A -> Prop) (u : type686 A) : (term238 A u Q _60087) = (term239 A Q _60087 u).
Proof. exact (MK_COMB (@lem4845452) (@lem4845446 A Q _60087 u)). Qed.
Lemma lem4845459 {A : Type'} (Q : type686 A) (_60087 : A -> Prop) (u : type686 A) : (term236 A Q _60087 u) = (term236 A Q _60087 u).
Proof. exact (eq_refl (term236 A Q _60087 u)). Qed.
Lemma lem4845460 {A : Type'} (Q : type686 A) (_60087 : A -> Prop) (u : type686 A) : ((term57 A u Q _60087) = (term236 A Q _60087 u)) = ((term236 A Q _60087 u) = (term236 A Q _60087 u)).
Proof. exact (MK_COMB (@lem4845453 A Q _60087 u) (@lem4845459 A Q _60087 u)). Qed.
Lemma lem4845462 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4845463 (x : Prop) : (x = x) = True.
Proof. exact (@lem4845462 Prop x). Qed.
Lemma lem4845464 {A : Type'} (Q : type686 A) (_60087 : A -> Prop) (u : type686 A) : ((term236 A Q _60087 u) = (term236 A Q _60087 u)) = True.
Proof. exact (@lem4845463 (term236 A Q _60087 u)). Qed.
Lemma lem4845465 {A : Type'} (Q : type686 A) (_60087 : A -> Prop) (u : type686 A) : ((term57 A u Q _60087) = (term236 A Q _60087 u)) = True.
Proof. exact (TRANS (@lem4845460 A Q _60087 u) (@lem4845464 A Q _60087 u)). Qed.
Lemma lem4845466 {A : Type'} (Q : type686 A) (_60087 : A -> Prop) (u : type686 A) : True = ((term57 A u Q _60087) = (term236 A Q _60087 u)).
Proof. exact (SYM (@lem4845465 A Q _60087 u)). Qed.
Lemma lem4845467 {A : Type'} (Q : type686 A) (_60087 : A -> Prop) (u : type686 A) : (term57 A u Q _60087) = (term236 A Q _60087 u).
Proof. exact (EQ_MP (@lem4845466 A Q _60087 u) (@lem0)). Qed.
Lemma lem4845468 {A : Type'} (_60087 : A -> Prop) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term236 A Q _60087 u.
Proof. exact (EQ_MP (@lem4845467 A Q _60087 u) (@lem4845227 A _60087 P u s Q Q' h1)). Qed.
Lemma lem4845470 (b : Prop) (a : Prop) : (a \/ b) = (term218 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4845471 {A : Type'} (u : type686 A) (Q : type686 A) (_60087 : A -> Prop) : (term236 A Q _60087 u) = (term240 A u Q _60087).
Proof. exact (@lem4845470 (term237 A _60087 u) (Q _60087)). Qed.
Lemma lem4845473 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4845474 {A : Type'} (_60087 : A -> Prop) (u : type686 A) : (term241 A _60087 u) = (@IN (A -> Prop) _60087 u).
Proof. exact (@lem4845473 (@IN (A -> Prop) _60087 u)). Qed.
Lemma lem4845475 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4845476 {A : Type'} (_60087 : A -> Prop) (u : type686 A) : (term242 A _60087 u) = (term243 A _60087 u).
Proof. exact (MK_COMB (@lem4845475) (@lem4845474 A _60087 u)). Qed.
Lemma lem4845477 {A : Type'} (Q : type686 A) (_60087 : A -> Prop) : (Q _60087) = (Q _60087).
Proof. exact (eq_refl (Q _60087)). Qed.
Lemma lem4845478 {A : Type'} (u : type686 A) (Q : type686 A) (_60087 : A -> Prop) : (term240 A u Q _60087) = (term45 A u Q _60087).
Proof. exact (MK_COMB (@lem4845476 A _60087 u) (@lem4845477 A Q _60087)). Qed.
Lemma lem4845479 {A : Type'} (u : type686 A) (Q : type686 A) (_60087 : A -> Prop) : (term236 A Q _60087 u) = (term45 A u Q _60087).
Proof. exact (TRANS (@lem4845471 A u Q _60087) (@lem4845478 A u Q _60087)). Qed.
Lemma lem4845482 {A : Type'} (_60087 : A -> Prop) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term45 A u Q _60087.
Proof. exact (EQ_MP (@lem4845479 A u Q _60087) (@lem4845468 A _60087 P u s Q Q' h1)). Qed.
Lemma lem4845483 {A : Type'} (_60087 : A -> Prop) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term45 A u Q _60087.
Proof. exact (@lem4845482 A _60087 P u s Q Q' h1). Qed.
Lemma lem4845484 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term244 A Q c u.
Proof. exact (@lem4845483 A (c u) P u s Q Q' h1). Qed.
Lemma lem4845487 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term245 A Q c u.
Proof. exact (@lem4845484 A c P u s Q Q' h2 (@lem4845439 A c P u s Q Q' h1 h2)). Qed.
Lemma lem4845488 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term246 A Q c u.
Proof. exact (fun h0 : term185 A Q c u => @lem4845487 A c P u s Q Q' h1 h2). Qed.
Lemma lem4845490 (p : Prop) : (term210 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4845491 {A : Type'} (Q : type686 A) (c : type178 A) (u : type686 A) : (term246 A Q c u) = (term245 A Q c u).
Proof. exact (@lem4845490 (term245 A Q c u)). Qed.
Lemma lem4845492 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term245 A Q c u.
Proof. exact (EQ_MP (@lem4845491 A Q c u) (@lem4845488 A c P u s Q Q' h1 h2)). Qed.
Lemma lem4845498 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4845499 {A : Type'} (Q' : type686 A) (Q : type686 A) (_60086 : A -> Prop) : (term65 A Q Q' _60086) = (term247 A Q' Q _60086).
Proof. exact (@lem4845498 (Q' _60086) (term248 A Q _60086)). Qed.
Lemma lem4845505 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4845506 {A : Type'} (Q' : type686 A) (Q : type686 A) (_60086 : A -> Prop) : (term249 A Q Q' _60086) = (term250 A Q' Q _60086).
Proof. exact (MK_COMB (@lem4845505) (@lem4845499 A Q' Q _60086)). Qed.
Lemma lem4845512 {A : Type'} (Q' : type686 A) (Q : type686 A) (_60086 : A -> Prop) : (term247 A Q' Q _60086) = (term247 A Q' Q _60086).
Proof. exact (eq_refl (term247 A Q' Q _60086)). Qed.
Lemma lem4845513 {A : Type'} (Q' : type686 A) (Q : type686 A) (_60086 : A -> Prop) : ((term65 A Q Q' _60086) = (term247 A Q' Q _60086)) = ((term247 A Q' Q _60086) = (term247 A Q' Q _60086)).
Proof. exact (MK_COMB (@lem4845506 A Q' Q _60086) (@lem4845512 A Q' Q _60086)). Qed.
Lemma lem4845515 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4845516 (x : Prop) : (x = x) = True.
Proof. exact (@lem4845515 Prop x). Qed.
Lemma lem4845517 {A : Type'} (Q' : type686 A) (Q : type686 A) (_60086 : A -> Prop) : ((term247 A Q' Q _60086) = (term247 A Q' Q _60086)) = True.
Proof. exact (@lem4845516 (term247 A Q' Q _60086)). Qed.
Lemma lem4845518 {A : Type'} (Q' : type686 A) (Q : type686 A) (_60086 : A -> Prop) : ((term65 A Q Q' _60086) = (term247 A Q' Q _60086)) = True.
Proof. exact (TRANS (@lem4845513 A Q' Q _60086) (@lem4845517 A Q' Q _60086)). Qed.
Lemma lem4845519 {A : Type'} (Q' : type686 A) (Q : type686 A) (_60086 : A -> Prop) : True = ((term65 A Q Q' _60086) = (term247 A Q' Q _60086)).
Proof. exact (SYM (@lem4845518 A Q' Q _60086)). Qed.
Lemma lem4845520 {A : Type'} (Q' : type686 A) (Q : type686 A) (_60086 : A -> Prop) : (term65 A Q Q' _60086) = (term247 A Q' Q _60086).
Proof. exact (EQ_MP (@lem4845519 A Q' Q _60086) (@lem0)). Qed.
Lemma lem4845521 {A : Type'} (_60086 : A -> Prop) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term247 A Q' Q _60086.
Proof. exact (EQ_MP (@lem4845520 A Q' Q _60086) (@lem4845199 A _60086 P u s Q Q' h1)). Qed.
Lemma lem4845523 (b : Prop) (a : Prop) : (a \/ b) = (term218 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4845524 {A : Type'} (Q : type686 A) (Q' : type686 A) (_60086 : A -> Prop) : (term247 A Q' Q _60086) = (term251 A Q Q' _60086).
Proof. exact (@lem4845523 (term248 A Q _60086) (Q' _60086)). Qed.
Lemma lem4845526 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4845527 {A : Type'} (Q : type686 A) (_60086 : A -> Prop) : (term252 A Q _60086) = (Q _60086).
Proof. exact (@lem4845526 (Q _60086)). Qed.
Lemma lem4845528 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4845529 {A : Type'} (Q : type686 A) (_60086 : A -> Prop) : (term253 A Q _60086) = (term254 A Q _60086).
Proof. exact (MK_COMB (@lem4845528) (@lem4845527 A Q _60086)). Qed.
Lemma lem4845530 {A : Type'} (Q' : type686 A) (_60086 : A -> Prop) : (Q' _60086) = (Q' _60086).
Proof. exact (eq_refl (Q' _60086)). Qed.
Lemma lem4845531 {A : Type'} (Q : type686 A) (Q' : type686 A) (_60086 : A -> Prop) : (term251 A Q Q' _60086) = (term53 A Q Q' _60086).
Proof. exact (MK_COMB (@lem4845529 A Q _60086) (@lem4845530 A Q' _60086)). Qed.
Lemma lem4845532 {A : Type'} (Q : type686 A) (Q' : type686 A) (_60086 : A -> Prop) : (term247 A Q' Q _60086) = (term53 A Q Q' _60086).
Proof. exact (TRANS (@lem4845524 A Q Q' _60086) (@lem4845531 A Q Q' _60086)). Qed.
Lemma lem4845535 {A : Type'} (_60086 : A -> Prop) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term53 A Q Q' _60086.
Proof. exact (EQ_MP (@lem4845532 A Q Q' _60086) (@lem4845521 A _60086 P u s Q Q' h1)). Qed.
Lemma lem4845536 {A : Type'} (_60086 : A -> Prop) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term53 A Q Q' _60086.
Proof. exact (@lem4845535 A _60086 P u s Q Q' h1). Qed.
Lemma lem4845537 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term255 A Q Q' c u.
Proof. exact (@lem4845536 A (c u) P u s Q Q' h1). Qed.
Lemma lem4845540 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term245 A Q' c u.
Proof. exact (@lem4845537 A c P u s Q Q' h2 (@lem4845492 A c P u s Q Q' h1 h2)). Qed.
Lemma lem4845541 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term246 A Q' c u.
Proof. exact (fun h0 : term185 A Q' c u => @lem4845540 A c P u s Q Q' h1 h2). Qed.
Lemma lem4845543 (p : Prop) : (term210 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4845544 {A : Type'} (Q' : type686 A) (c : type178 A) (u : type686 A) : (term246 A Q' c u) = (term245 A Q' c u).
Proof. exact (@lem4845543 (term245 A Q' c u)). Qed.
Lemma lem4845545 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term245 A Q' c u.
Proof. exact (EQ_MP (@lem4845544 A Q' c u) (@lem4845541 A c P u s Q Q' h1 h2)). Qed.
Lemma lem4845547 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem21386 (A -> Prop) x). Qed.
Lemma lem4845548 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem4845547 A x). Qed.
Lemma lem4845549 {A : Type'} (u : type686 A) : (@INTERS A u) = (@INTERS A u).
Proof. exact (@lem4845548 A (@INTERS A u)). Qed.
Lemma lem4845550 {A : Type'} (u : type686 A) : term211 A u.
Proof. exact (fun h0 : term212 A u => @lem4845549 A u). Qed.
Lemma lem4845552 (p : Prop) : (term210 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4845553 {A : Type'} (u : type686 A) : (term211 A u) = ((@INTERS A u) = (@INTERS A u)).
Proof. exact (@lem4845552 ((@INTERS A u) = (@INTERS A u))). Qed.
Lemma lem4845554 {A : Type'} (u : type686 A) : (@INTERS A u) = (@INTERS A u).
Proof. exact (EQ_MP (@lem4845553 A u) (@lem4845550 A u)). Qed.
Lemma lem4845556 (a : Prop) (b : Prop) : (term256 a b) = (term257 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4845557 {A : Type'} (Q' : type686 A) (c : type178 A) (_60085 : type686 A) (u : type686 A) : (term258 A Q' c _60085 u) = (term259 A Q' c _60085 u).
Proof. exact (@lem4845556 (term245 A Q' c _60085) ((@INTERS A _60085) = (@INTERS A u))). Qed.
Lemma lem4845558 {A : Type'} (P : type180 A) (_60085 : type686 A) : (term106 A P _60085) = (term106 A P _60085).
Proof. exact (eq_refl (term106 A P _60085)). Qed.
Lemma lem4845559 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (_60085 : type686 A) (u : type686 A) : (term206 A P Q' c _60085 u) = (term260 A P Q' c _60085 u).
Proof. exact (MK_COMB (@lem4845558 A P _60085) (@lem4845557 A Q' c _60085 u)). Qed.
Lemma lem4845561 (a : Prop) (b : Prop) : (term256 a b) = (term257 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4845562 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (_60085 : type686 A) (u : type686 A) : (term260 A P Q' c _60085 u) = (term261 A P Q' c _60085 u).
Proof. exact (@lem4845561 (P _60085) (term262 A Q' c _60085 u)). Qed.
Lemma lem4845563 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (_60085 : type686 A) (u : type686 A) : (term206 A P Q' c _60085 u) = (term261 A P Q' c _60085 u).
Proof. exact (TRANS (@lem4845559 A P Q' c _60085 u) (@lem4845562 A P Q' c _60085 u)). Qed.
Lemma lem4845565 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4845566 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (_60085 : type686 A) (u : type686 A) : (term261 A P Q' c _60085 u) = (term263 A P Q' c _60085 u).
Proof. exact (@lem4845565 (term264 A P Q' c _60085 u)). Qed.
Lemma lem4845567 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (_60085 : type686 A) (u : type686 A) : (term206 A P Q' c _60085 u) = (term263 A P Q' c _60085 u).
Proof. exact (TRANS (@lem4845563 A P Q' c _60085 u) (@lem4845566 A P Q' c _60085 u)). Qed.
Lemma lem4845569 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term265 A Q' c u.
Proof. exact (conj (@lem4845545 A c P u s Q Q' h1 h2) (@lem4845554 A u)). Qed.
Lemma lem4845570 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term266 A P Q' c u.
Proof. exact (conj (@lem4845335 A P u s Q Q' h2) (@lem4845569 A c P u s Q Q' h1 h2)). Qed.
Lemma lem4845572 {A : Type'} (_60085 : type686 A) (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term263 A P Q' c _60085 u.
Proof. exact (EQ_MP (@lem4845567 A P Q' c _60085 u) (@lem4845253 A _60085 c P u s Q Q' h1 h2)). Qed.
Lemma lem4845573 {A : Type'} (_60085 : type686 A) (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term263 A P Q' c _60085 u.
Proof. exact (@lem4845572 A _60085 c P u s Q Q' h1 h2). Qed.
Lemma lem4845574 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term267 A P Q' c u.
Proof. exact (@lem4845573 A u c P u s Q Q' h1 h2). Qed.
Lemma lem4845577 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : False.
Proof. exact (@lem4845574 A c P u s Q Q' h1 h2 (@lem4845570 A c P u s Q Q' h1 h2)). Qed.
Lemma lem4845578 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term268.
Proof. exact (fun h0 : ~ False => @lem4845577 A c P u s Q Q' h1 h2). Qed.
Lemma lem4845580 (p : Prop) : (term210 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4845581 : term268 = False.
Proof. exact (@lem4845580 False). Qed.
Lemma lem4845583 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : False.
Proof. exact (EQ_MP (@lem4845581) (@lem4845578 A c P u s Q Q' h1 h2)). Qed.
Lemma lem4845584 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : (term85 A P u s Q Q') = False.
Proof. exact (prop_ext (fun h3 : term85 A P u s Q Q' => @lem4845583 A c P u s Q Q' h1 h2) (fun h3 : False => @lem4845048 A P u s Q Q' h2)). Qed.
Lemma lem4845585 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : False.
Proof. exact (EQ_MP (@lem4845584 A c P u s Q Q' h1 h2) (@lem4845048 A P u s Q Q' h2)). Qed.
Lemma lem4845586 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : (term178 A P Q' c s) = False.
Proof. exact (prop_ext (fun h3 : term178 A P Q' c s => @lem4845585 A c P u s Q Q' h1 h2) (fun h3 : False => @lem4844998 A P Q' c s h1)). Qed.
Lemma lem4845587 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : False.
Proof. exact (EQ_MP (@lem4845586 A c P u s Q Q' h1 h2) (@lem4844998 A P Q' c s h1)). Qed.
Lemma lem4845588 {A : Type'} (c : type178 A) (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term16 A P s Q Q') : False.
Proof. exact (ex_elim (@lem4844735 A P s Q Q' h2) (fun u : type686 A => fun h0 : term87 A P s Q Q' u => @lem4845587 A c P u s Q Q' h1 h0)). Qed.
Lemma lem4845589 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term56 A P Q' s) (h2 : term16 A P s Q Q') : False.
Proof. exact (ex_elim (@lem4844955 A P Q' s h1) (fun c : type178 A => fun h0 : term180 A P Q' s c => @lem4845588 A c P s Q Q' h0 h2)). Qed.
Lemma lem4845590 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term56 A P Q' s) (h2 : term16 A P s Q Q') : (term56 A P Q' s) = False.
Proof. exact (prop_ext (fun h3 : term56 A P Q' s => @lem4845589 A P s Q Q' h1 h2) (fun h3 : False => @lem4844581 A P Q' s h1)). Qed.
Lemma lem4845591 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term56 A P Q' s) (h2 : term16 A P s Q Q') : False.
Proof. exact (EQ_MP (@lem4845590 A P s Q Q' h1 h2) (@lem4844581 A P Q' s h1)). Qed.
Lemma lem4845592 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term16 A P s Q Q') : term55 A P Q' s.
Proof. exact (fun h0 : term56 A P Q' s => @lem4845591 A P s Q Q' h0 h1). Qed.
Lemma lem4845593 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term16 A P s Q Q') : term8 A P Q' s.
Proof. exact (EQ_MP (@lem4844580 A P Q' s) (@lem4845592 A P s Q Q' h1)). Qed.
Lemma lem4845594 {A : Type'} (Q : type686 A) (P : type180 A) (Q' : type686 A) (s : A -> Prop) : term20 A Q P Q' s.
Proof. exact (fun h0 : term16 A P s Q Q' => @lem4845593 A P s Q Q' h0). Qed.
Lemma lem4845599 {A : Type'} (Q : type686 A) (P : type180 A) (Q' : type686 A) : term24 A Q P Q'.
Proof. exact (fun s : A -> Prop => @lem4845594 A Q P Q' s). Qed.
Lemma lem4845604 {A : Type'} (Q : type686 A) (P : type180 A) : term28 A Q P.
Proof. exact (fun Q' : type686 A => @lem4845599 A Q P Q'). Qed.
Lemma lem4845609 {A : Type'} (P : type180 A) : term32 A P.
Proof. exact (fun Q : type686 A => @lem4845604 A Q P). Qed.
Lemma lem4845614 {A : Type'} : term36 A.
Proof. exact (fun P : type180 A => @lem4845609 A P). Qed.
Lemma lem4845615 {A : Type'} : term38 A.
Proof. exact (EQ_MP (@lem4844575 A) (@lem4845614 A)). Qed.
Lemma lem4845617 {A : Type'} : term38 A.
Proof. exact (@lem4844322 A (@lem4845615 A)). Qed.
Lemma lem4845618 {A : Type'} (h1 : term39 A) : False.
Proof. exact (@lem4845617 A (@lem4844306 A h1)). Qed.
Lemma lem4845619 {A : Type'} (h1 : term39 A) : (term39 A) = False.
Proof. exact (prop_ext (fun h2 : term39 A => @lem4845618 A h1) (fun h2 : False => @lem4844306 A h1)). Qed.
Lemma lem4845620 {A : Type'} (h1 : term39 A) : False.
Proof. exact (EQ_MP (@lem4845619 A h1) (@lem4844306 A h1)). Qed.
Lemma lem4845621 {A : Type'} : term38 A.
Proof. exact (fun h0 : term39 A => @lem4845620 A h0). Qed.
Lemma lem4845622 {A : Type'} : term36 A.
Proof. exact (EQ_MP (@lem4844305 A) (@lem4845621 A)). Qed.
Lemma lem4845623 {A : Type'} : term35 A.
Proof. exact (EQ_MP (@lem4844301 A) (@lem4845622 A)). Qed.
