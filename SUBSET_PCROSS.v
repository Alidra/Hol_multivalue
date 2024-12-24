Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUBSET_PCROSS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EXTENSION_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import PASTECART_IN_PCROSS_spec.
Require Import SUBSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm1857_spec.
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
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm4211_spec.
Require Import thm7660850_spec.
Require Import thm7662539_spec.
Require Import thm82_spec.
Lemma lem8006150 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem8006151 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem8006152 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem8006151 t1) (@lem8006150 t1)). Qed.
Lemma lem8006153 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem8006152 t1 t2). Qed.
Lemma lem8006154 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem8006155 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem8006154 t1 t2) (@lem8006153 t1 t2)). Qed.
Lemma lem8006156 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem8006155 t1 t2 t3). Qed.
Lemma lem8006157 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem8006158 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem8006157 t1 t2 t3) (@lem8006156 t1 t2 t3)). Qed.
Lemma lem8006159 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem8006158 t1 t2 t3)). Qed.
Lemma lem8006160 {A : Type'} (x : A) : term7 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem8006161 {A : Type'} (x : A) : (term7 A x) = (term8 A x).
Proof. exact (eq_refl (term7 A x)). Qed.
Lemma lem8006162 {A : Type'} (x : A) : term8 A x.
Proof. exact (EQ_MP (@lem8006161 A x) (@lem8006160 A x)). Qed.
Lemma lem8006163 {A : Type'} (x : A) : term9 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem8006165 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : term10 _141927 _141928 _141929 s.
Proof. exact (@lem8004229 _141927 _141928 _141929 s). Qed.
Lemma lem8006166 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : (term10 _141927 _141928 _141929 s) = (term11 _141927 _141928 _141929 s).
Proof. exact (eq_refl (term10 _141927 _141928 _141929 s)). Qed.
Lemma lem8006167 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : term11 _141927 _141928 _141929 s.
Proof. exact (EQ_MP (@lem8006166 _141927 _141928 _141929 s) (@lem8006165 _141927 _141928 _141929 s)). Qed.
Lemma lem8006168 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term12 _141927 _141928 _141929 s t.
Proof. exact (@lem8006167 _141927 _141928 _141929 s t). Qed.
Lemma lem8006169 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term12 _141927 _141928 _141929 s t) = (term13 _141927 _141928 _141929 s t).
Proof. exact (eq_refl (term12 _141927 _141928 _141929 s t)). Qed.
Lemma lem8006170 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term13 _141927 _141928 _141929 s t.
Proof. exact (EQ_MP (@lem8006169 _141927 _141928 _141929 s t) (@lem8006168 _141927 _141928 _141929 s t)). Qed.
Lemma lem8006171 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) (x : cart _141927 _141928) : term14 _141927 _141928 _141929 s t x.
Proof. exact (@lem8006170 _141927 _141928 _141929 s t x). Qed.
Lemma lem8006172 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term14 _141927 _141928 _141929 s t x) = (term15 _141927 _141928 _141929 x s t).
Proof. exact (eq_refl (term14 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8006173 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term15 _141927 _141928 _141929 x s t.
Proof. exact (EQ_MP (@lem8006172 _141927 _141928 _141929 x s t) (@lem8006171 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8006174 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) (y : cart _141927 _141929) : term16 _141927 _141928 _141929 x s t y.
Proof. exact (@lem8006173 _141927 _141928 _141929 x s t y). Qed.
Lemma lem8006175 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term16 _141927 _141928 _141929 x s t y) = ((term17 _141927 _141928 _141929 x y s t) = (term18 _141927 _141928 _141929 x s y t)).
Proof. exact (eq_refl (term16 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8006177 {A : Type'} (s : A -> Prop) : term19 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem8006178 {A : Type'} (s : A -> Prop) : (term19 A s) = (term20 A s).
Proof. exact (eq_refl (term19 A s)). Qed.
Lemma lem8006179 {A : Type'} (s : A -> Prop) : term20 A s.
Proof. exact (EQ_MP (@lem8006178 A s) (@lem8006177 A s)). Qed.
Lemma lem8006180 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term21 A s t.
Proof. exact (@lem8006179 A s t). Qed.
Lemma lem8006181 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term21 A s t) = ((@SUBSET A s t) = (term22 A s t)).
Proof. exact (eq_refl (term21 A s t)). Qed.
Lemma lem8006192 {A : Type'} (s : A -> Prop) : term23 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem8006193 {A : Type'} (s : A -> Prop) : (term23 A s) = (term24 A s).
Proof. exact (eq_refl (term23 A s)). Qed.
Lemma lem8006194 {A : Type'} (s : A -> Prop) : term24 A s.
Proof. exact (EQ_MP (@lem8006193 A s) (@lem8006192 A s)). Qed.
Lemma lem8006195 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term25 A s t.
Proof. exact (@lem8006194 A s t). Qed.
Lemma lem8006196 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term25 A s t) = ((s = t) = (term26 A s t)).
Proof. exact (eq_refl (term25 A s t)). Qed.
Lemma lem8006233 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term22 A s t).
Proof. exact (EQ_MP (@lem8006181 A s t) (@lem8006180 A s t)). Qed.
Lemma lem8006234 {_142062 _142063 _142064 : Type'} (s : type16 _142062 _142063 _142064) (t : type16 _142062 _142063 _142064) : (@SUBSET (cart _142062 (finite_sum _142063 _142064)) s t) = (term27 _142062 _142063 _142064 s t).
Proof. exact (@lem8006233 (type2 _142062 _142063 _142064) s t). Qed.
Lemma lem8006235 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term28 _142062 _142063 _142064 s t s' t') = (term29 _142062 _142063 _142064 s t s' t').
Proof. exact (@lem8006234 _142062 _142063 _142064 (@PCROSS _142062 _142063 _142064 s t) (@PCROSS _142062 _142063 _142064 s' t')). Qed.
Lemma lem8006241 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term30 _140454 _140455 _140456 P) = (term31 _140454 _140455 _140456 P).
Proof. exact (EQ_MP (@lem7660850 _140454 _140455 _140456 P) (@lem7662539 _140454 _140455 _140456 P)). Qed.
Lemma lem8006242 {_142062 _142063 _142064 : Type'} (P : type16 _142062 _142063 _142064) : (term30 _142062 _142063 _142064 P) = (term31 _142062 _142063 _142064 P).
Proof. exact (@lem8006241 _142062 _142063 _142064 P). Qed.
Lemma lem8006243 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term32 _142062 _142063 _142064 s t s' t') = (term33 _142062 _142063 _142064 s t s' t').
Proof. exact (@lem8006242 _142062 _142063 _142064 (term34 _142062 _142063 _142064 s t s' t')). Qed.
Lemma lem8006244 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : type2 _142062 _142063 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term35 _142062 _142063 _142064 s t s' t' x) = (term36 _142062 _142063 _142064 s t x s' t').
Proof. exact (eq_refl (term35 _142062 _142063 _142064 s t s' t' x)). Qed.
Lemma lem8006245 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term37 _142062 _142063 _142064 s t s' t') = (term34 _142062 _142063 _142064 s t s' t').
Proof. exact (fun_ext (fun x : type2 _142062 _142063 _142064 => @lem8006244 _142062 _142063 _142064 s t x s' t')). Qed.
Lemma lem8006246 {_142062 _142063 _142064 : Type'} : (@all (cart _142062 (finite_sum _142063 _142064))) = (@all (cart _142062 (finite_sum _142063 _142064))).
Proof. exact (eq_refl (@all (cart _142062 (finite_sum _142063 _142064)))). Qed.
Lemma lem8006247 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term32 _142062 _142063 _142064 s t s' t') = (term29 _142062 _142063 _142064 s t s' t').
Proof. exact (MK_COMB (@lem8006246 _142062 _142063 _142064) (@lem8006245 _142062 _142063 _142064 s t s' t')). Qed.
Lemma lem8006248 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8006249 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term38 _142062 _142063 _142064 s t s' t') = (term39 _142062 _142063 _142064 s t s' t').
Proof. exact (MK_COMB (@lem8006248) (@lem8006247 _142062 _142063 _142064 s t s' t')). Qed.
Lemma lem8006250 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (y : cart _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term40 _142062 _142063 _142064 s t s' t' x y) = (term41 _142062 _142063 _142064 s t x y s' t').
Proof. exact (eq_refl (term40 _142062 _142063 _142064 s t s' t' x y)). Qed.
Lemma lem8006251 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term42 _142062 _142063 _142064 s t s' t' x) = (term43 _142062 _142063 _142064 s t x s' t').
Proof. exact (fun_ext (fun y : cart _142062 _142064 => @lem8006250 _142062 _142063 _142064 s t x y s' t')). Qed.
Lemma lem8006252 {_142062 _142064 : Type'} : (@all (cart _142062 _142064)) = (@all (cart _142062 _142064)).
Proof. exact (eq_refl (@all (cart _142062 _142064))). Qed.
Lemma lem8006253 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term44 _142062 _142063 _142064 s t s' t' x) = (term45 _142062 _142063 _142064 s t x s' t').
Proof. exact (MK_COMB (@lem8006252 _142062 _142064) (@lem8006251 _142062 _142063 _142064 s t x s' t')). Qed.
Lemma lem8006254 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term46 _142062 _142063 _142064 s t s' t') = (term47 _142062 _142063 _142064 s t s' t').
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8006253 _142062 _142063 _142064 s t x s' t')). Qed.
Lemma lem8006255 {_142062 _142063 : Type'} : (@all (cart _142062 _142063)) = (@all (cart _142062 _142063)).
Proof. exact (eq_refl (@all (cart _142062 _142063))). Qed.
Lemma lem8006256 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term33 _142062 _142063 _142064 s t s' t') = (term48 _142062 _142063 _142064 s t s' t').
Proof. exact (MK_COMB (@lem8006255 _142062 _142063) (@lem8006254 _142062 _142063 _142064 s t s' t')). Qed.
Lemma lem8006257 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : ((term32 _142062 _142063 _142064 s t s' t') = (term33 _142062 _142063 _142064 s t s' t')) = ((term29 _142062 _142063 _142064 s t s' t') = (term48 _142062 _142063 _142064 s t s' t')).
Proof. exact (MK_COMB (@lem8006249 _142062 _142063 _142064 s t s' t') (@lem8006256 _142062 _142063 _142064 s t s' t')). Qed.
Lemma lem8006258 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term29 _142062 _142063 _142064 s t s' t') = (term48 _142062 _142063 _142064 s t s' t').
Proof. exact (EQ_MP (@lem8006257 _142062 _142063 _142064 s t s' t') (@lem8006243 _142062 _142063 _142064 s t s' t')). Qed.
Lemma lem8006274 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term49 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem8006275 (p : Prop) (q : Prop) (p' : Prop) : term50 p q p'.
Proof. exact (fun q' : Prop => @lem8006274 p q p' q'). Qed.
Lemma lem8006276 (p : Prop) (q : Prop) : term51 p q.
Proof. exact (fun p' : Prop => @lem8006275 p q p'). Qed.
Lemma lem8006277 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (y : cart _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : term52 _142062 _142063 _142064 s t x y s' t'.
Proof. exact (@lem8006276 (term17 _142062 _142063 _142064 x y s t) (term17 _142062 _142063 _142064 x y s' t')). Qed.
Lemma lem8006278 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (y : cart _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) (p' : Prop) : term53 _142062 _142063 _142064 s t x y s' t' p'.
Proof. exact (@lem8006277 _142062 _142063 _142064 s t x y s' t' p'). Qed.
Lemma lem8006279 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (y : cart _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) (p' : Prop) : (term53 _142062 _142063 _142064 s t x y s' t' p') = (term54 _142062 _142063 _142064 s t x y s' t' p').
Proof. exact (eq_refl (term53 _142062 _142063 _142064 s t x y s' t' p')). Qed.
Lemma lem8006280 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (y : cart _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) (p' : Prop) : term54 _142062 _142063 _142064 s t x y s' t' p'.
Proof. exact (EQ_MP (@lem8006279 _142062 _142063 _142064 s t x y s' t' p') (@lem8006278 _142062 _142063 _142064 s t x y s' t' p')). Qed.
Lemma lem8006281 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (y : cart _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) (p' : Prop) (q' : Prop) : term55 _142062 _142063 _142064 s t x y s' t' p' q'.
Proof. exact (@lem8006280 _142062 _142063 _142064 s t x y s' t' p' q'). Qed.
Lemma lem8006282 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (y : cart _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) (p' : Prop) (q' : Prop) : (term55 _142062 _142063 _142064 s t x y s' t' p' q') = (term56 _142062 _142063 _142064 s t x y s' t' p' q').
Proof. exact (eq_refl (term55 _142062 _142063 _142064 s t x y s' t' p' q')). Qed.
Lemma lem8006283 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (y : cart _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) (p' : Prop) (q' : Prop) : term56 _142062 _142063 _142064 s t x y s' t' p' q'.
Proof. exact (EQ_MP (@lem8006282 _142062 _142063 _142064 s t x y s' t' p' q') (@lem8006281 _142062 _142063 _142064 s t x y s' t' p' q')). Qed.
Lemma lem8006285 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term17 _141927 _141928 _141929 x y s t) = (term18 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8006175 _141927 _141928 _141929 x s y t) (@lem8006174 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8006286 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (y : cart _142062 _142064) (t : type24 _142062 _142064) : (term17 _142062 _142063 _142064 x y s t) = (term18 _142062 _142063 _142064 x s y t).
Proof. exact (@lem8006285 _142062 _142063 _142064 x s y t). Qed.
Lemma lem8006289 {_142062 _142063 _142064 : Type'} (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) (x : cart _142062 _142063) (s : type24 _142062 _142063) (y : cart _142062 _142064) (t : type24 _142062 _142064) (q' : Prop) : term57 _142062 _142063 _142064 s' t' x s y t q'.
Proof. exact (@lem8006283 _142062 _142063 _142064 s t x y s' t' (term18 _142062 _142063 _142064 x s y t) q'). Qed.
Lemma lem8006290 {_142062 _142063 _142064 : Type'} (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) (x : cart _142062 _142063) (s : type24 _142062 _142063) (y : cart _142062 _142064) (t : type24 _142062 _142064) (q' : Prop) : term58 _142062 _142063 _142064 s' t' x s y t q'.
Proof. exact (@lem8006289 _142062 _142063 _142064 s' t' x s y t q' (@lem8006286 _142062 _142063 _142064 x s y t)). Qed.
Lemma lem8006299 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term17 _141927 _141928 _141929 x y s t) = (term18 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8006175 _141927 _141928 _141929 x s y t) (@lem8006174 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8006300 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (y : cart _142062 _142064) (t : type24 _142062 _142064) : (term17 _142062 _142063 _142064 x y s t) = (term18 _142062 _142063 _142064 x s y t).
Proof. exact (@lem8006299 _142062 _142063 _142064 x s y t). Qed.
Lemma lem8006301 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s' : type24 _142062 _142063) (y : cart _142062 _142064) (t' : type24 _142062 _142064) : (term17 _142062 _142063 _142064 x y s' t') = (term18 _142062 _142063 _142064 x s' y t').
Proof. exact (@lem8006300 _142062 _142063 _142064 x s' y t'). Qed.
Lemma lem8006304 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (y : cart _142062 _142064) (t' : type24 _142062 _142064) : term59 _142062 _142063 _142064 s t x s' y t'.
Proof. exact (fun h0 : term18 _142062 _142063 _142064 x s y t => @lem8006301 _142062 _142063 _142064 x s' y t'). Qed.
Lemma lem8006305 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (y : cart _142062 _142064) (t' : type24 _142062 _142064) : term60 _142062 _142063 _142064 s t x s' y t'.
Proof. exact (@lem8006290 _142062 _142063 _142064 s' t' x s y t (term18 _142062 _142063 _142064 x s' y t')). Qed.
Lemma lem8006306 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (y : cart _142062 _142064) (t' : type24 _142062 _142064) : (term41 _142062 _142063 _142064 s t x y s' t') = (term61 _142062 _142063 _142064 s t x s' y t').
Proof. exact (@lem8006305 _142062 _142063 _142064 s t x s' y t' (@lem8006304 _142062 _142063 _142064 s t x s' y t')). Qed.
Lemma lem8006342 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term43 _142062 _142063 _142064 s t x s' t') = (term62 _142062 _142063 _142064 s t x s' t').
Proof. exact (fun_ext (fun y : cart _142062 _142064 => @lem8006306 _142062 _142063 _142064 s t x s' y t')). Qed.
Lemma lem8006378 {_142062 _142064 : Type'} : (@all (cart _142062 _142064)) = (@all (cart _142062 _142064)).
Proof. exact (eq_refl (@all (cart _142062 _142064))). Qed.
Lemma lem8006379 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term45 _142062 _142063 _142064 s t x s' t') = (term63 _142062 _142063 _142064 s t x s' t').
Proof. exact (MK_COMB (@lem8006378 _142062 _142064) (@lem8006342 _142062 _142063 _142064 s t x s' t')). Qed.
Lemma lem8006421 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term47 _142062 _142063 _142064 s t s' t') = (term64 _142062 _142063 _142064 s t s' t').
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8006379 _142062 _142063 _142064 s t x s' t')). Qed.
Lemma lem8006463 {_142062 _142063 : Type'} : (@all (cart _142062 _142063)) = (@all (cart _142062 _142063)).
Proof. exact (eq_refl (@all (cart _142062 _142063))). Qed.
Lemma lem8006464 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term48 _142062 _142063 _142064 s t s' t') = (term65 _142062 _142063 _142064 s t s' t').
Proof. exact (MK_COMB (@lem8006463 _142062 _142063) (@lem8006421 _142062 _142063 _142064 s t s' t')). Qed.
Lemma lem8006512 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term29 _142062 _142063 _142064 s t s' t') = (term65 _142062 _142063 _142064 s t s' t').
Proof. exact (TRANS (@lem8006258 _142062 _142063 _142064 s t s' t') (@lem8006464 _142062 _142063 _142064 s t s' t')). Qed.
Lemma lem8006513 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term28 _142062 _142063 _142064 s t s' t') = (term65 _142062 _142063 _142064 s t s' t').
Proof. exact (TRANS (@lem8006235 _142062 _142063 _142064 s t s' t') (@lem8006512 _142062 _142063 _142064 s t s' t')). Qed.
Lemma lem8006514 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8006515 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term66 _142062 _142063 _142064 s t s' t') = (term67 _142062 _142063 _142064 s t s' t').
Proof. exact (MK_COMB (@lem8006514) (@lem8006513 _142062 _142063 _142064 s t s' t')). Qed.
Lemma lem8006568 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term26 A s t).
Proof. exact (EQ_MP (@lem8006196 A s t) (@lem8006195 A s t)). Qed.
Lemma lem8006569 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142063) : (s = t) = (term68 _142062 _142063 s t).
Proof. exact (@lem8006568 (cart _142062 _142063) s t). Qed.
Lemma lem8006570 {_142062 _142063 : Type'} (s : type24 _142062 _142063) : (s = (@EMPTY (cart _142062 _142063))) = (term69 _142062 _142063 s).
Proof. exact (@lem8006569 _142062 _142063 s (@EMPTY (cart _142062 _142063))). Qed.
Lemma lem8006582 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem8006163 A x (@lem8006162 A x)). Qed.
Lemma lem8006583 {_142062 _142063 : Type'} (x : cart _142062 _142063) : (@IN (cart _142062 _142063) x (@EMPTY (cart _142062 _142063))) = False.
Proof. exact (@lem8006582 (cart _142062 _142063) x). Qed.
Lemma lem8006584 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) : (term70 _142062 _142063 x s) = (term70 _142062 _142063 x s).
Proof. exact (eq_refl (term70 _142062 _142063 x s)). Qed.
Lemma lem8006585 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) : ((@IN (cart _142062 _142063) x s) = (@IN (cart _142062 _142063) x (@EMPTY (cart _142062 _142063)))) = ((@IN (cart _142062 _142063) x s) = False).
Proof. exact (MK_COMB (@lem8006584 _142062 _142063 x s) (@lem8006583 _142062 _142063 x)). Qed.
Lemma lem8006587 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem8006588 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) : ((@IN (cart _142062 _142063) x s) = False) = (term71 _142062 _142063 x s).
Proof. exact (@lem8006587 (@IN (cart _142062 _142063) x s)). Qed.
Lemma lem8006589 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) : ((@IN (cart _142062 _142063) x s) = (@IN (cart _142062 _142063) x (@EMPTY (cart _142062 _142063)))) = (term71 _142062 _142063 x s).
Proof. exact (TRANS (@lem8006585 _142062 _142063 x s) (@lem8006588 _142062 _142063 x s)). Qed.
Lemma lem8006590 {_142062 _142063 : Type'} (s : type24 _142062 _142063) : (term72 _142062 _142063 s) = (term73 _142062 _142063 s).
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8006589 _142062 _142063 x s)). Qed.
Lemma lem8006591 {_142062 _142063 : Type'} : (@all (cart _142062 _142063)) = (@all (cart _142062 _142063)).
Proof. exact (eq_refl (@all (cart _142062 _142063))). Qed.
Lemma lem8006592 {_142062 _142063 : Type'} (s : type24 _142062 _142063) : (term69 _142062 _142063 s) = (term74 _142062 _142063 s).
Proof. exact (MK_COMB (@lem8006591 _142062 _142063) (@lem8006590 _142062 _142063 s)). Qed.
Lemma lem8006599 {_142062 _142063 : Type'} (s : type24 _142062 _142063) : (s = (@EMPTY (cart _142062 _142063))) = (term74 _142062 _142063 s).
Proof. exact (TRANS (@lem8006570 _142062 _142063 s) (@lem8006592 _142062 _142063 s)). Qed.
Lemma lem8006600 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8006601 {_142062 _142063 : Type'} (s : type24 _142062 _142063) : (term75 _142062 _142063 s) = (term76 _142062 _142063 s).
Proof. exact (MK_COMB (@lem8006600) (@lem8006599 _142062 _142063 s)). Qed.
Lemma lem8006613 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term26 A s t).
Proof. exact (EQ_MP (@lem8006196 A s t) (@lem8006195 A s t)). Qed.
Lemma lem8006614 {_142062 _142064 : Type'} (s : type24 _142062 _142064) (t : type24 _142062 _142064) : (s = t) = (term68 _142062 _142064 s t).
Proof. exact (@lem8006613 (cart _142062 _142064) s t). Qed.
Lemma lem8006615 {_142062 _142064 : Type'} (t : type24 _142062 _142064) : (t = (@EMPTY (cart _142062 _142064))) = (term69 _142062 _142064 t).
Proof. exact (@lem8006614 _142062 _142064 t (@EMPTY (cart _142062 _142064))). Qed.
Lemma lem8006627 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem8006163 A x (@lem8006162 A x)). Qed.
Lemma lem8006628 {_142062 _142064 : Type'} (x : cart _142062 _142064) : (@IN (cart _142062 _142064) x (@EMPTY (cart _142062 _142064))) = False.
Proof. exact (@lem8006627 (cart _142062 _142064) x). Qed.
Lemma lem8006629 {_142062 _142064 : Type'} (x : cart _142062 _142064) (t : type24 _142062 _142064) : (term70 _142062 _142064 x t) = (term70 _142062 _142064 x t).
Proof. exact (eq_refl (term70 _142062 _142064 x t)). Qed.
Lemma lem8006630 {_142062 _142064 : Type'} (x : cart _142062 _142064) (t : type24 _142062 _142064) : ((@IN (cart _142062 _142064) x t) = (@IN (cart _142062 _142064) x (@EMPTY (cart _142062 _142064)))) = ((@IN (cart _142062 _142064) x t) = False).
Proof. exact (MK_COMB (@lem8006629 _142062 _142064 x t) (@lem8006628 _142062 _142064 x)). Qed.
Lemma lem8006632 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem8006633 {_142062 _142064 : Type'} (x : cart _142062 _142064) (t : type24 _142062 _142064) : ((@IN (cart _142062 _142064) x t) = False) = (term71 _142062 _142064 x t).
Proof. exact (@lem8006632 (@IN (cart _142062 _142064) x t)). Qed.
Lemma lem8006634 {_142062 _142064 : Type'} (x : cart _142062 _142064) (t : type24 _142062 _142064) : ((@IN (cart _142062 _142064) x t) = (@IN (cart _142062 _142064) x (@EMPTY (cart _142062 _142064)))) = (term71 _142062 _142064 x t).
Proof. exact (TRANS (@lem8006630 _142062 _142064 x t) (@lem8006633 _142062 _142064 x t)). Qed.
Lemma lem8006635 {_142062 _142064 : Type'} (t : type24 _142062 _142064) : (term72 _142062 _142064 t) = (term73 _142062 _142064 t).
Proof. exact (fun_ext (fun x : cart _142062 _142064 => @lem8006634 _142062 _142064 x t)). Qed.
Lemma lem8006636 {_142062 _142064 : Type'} : (@all (cart _142062 _142064)) = (@all (cart _142062 _142064)).
Proof. exact (eq_refl (@all (cart _142062 _142064))). Qed.
Lemma lem8006637 {_142062 _142064 : Type'} (t : type24 _142062 _142064) : (term69 _142062 _142064 t) = (term74 _142062 _142064 t).
Proof. exact (MK_COMB (@lem8006636 _142062 _142064) (@lem8006635 _142062 _142064 t)). Qed.
Lemma lem8006644 {_142062 _142064 : Type'} (t : type24 _142062 _142064) : (t = (@EMPTY (cart _142062 _142064))) = (term74 _142062 _142064 t).
Proof. exact (TRANS (@lem8006615 _142062 _142064 t) (@lem8006637 _142062 _142064 t)). Qed.
Lemma lem8006645 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8006646 {_142062 _142064 : Type'} (t : type24 _142062 _142064) : (term75 _142062 _142064 t) = (term76 _142062 _142064 t).
Proof. exact (MK_COMB (@lem8006645) (@lem8006644 _142062 _142064 t)). Qed.
Lemma lem8006656 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term22 A s t).
Proof. exact (EQ_MP (@lem8006181 A s t) (@lem8006180 A s t)). Qed.
Lemma lem8006657 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142063) : (@SUBSET (cart _142062 _142063) s t) = (term77 _142062 _142063 s t).
Proof. exact (@lem8006656 (cart _142062 _142063) s t). Qed.
Lemma lem8006658 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) : (@SUBSET (cart _142062 _142063) s s') = (term77 _142062 _142063 s s').
Proof. exact (@lem8006657 _142062 _142063 s s'). Qed.
Lemma lem8006688 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8006689 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) : (term78 _142062 _142063 s s') = (term79 _142062 _142063 s s').
Proof. exact (MK_COMB (@lem8006688) (@lem8006658 _142062 _142063 s s')). Qed.
Lemma lem8006720 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term22 A s t).
Proof. exact (EQ_MP (@lem8006181 A s t) (@lem8006180 A s t)). Qed.
Lemma lem8006721 {_142062 _142064 : Type'} (s : type24 _142062 _142064) (t : type24 _142062 _142064) : (@SUBSET (cart _142062 _142064) s t) = (term77 _142062 _142064 s t).
Proof. exact (@lem8006720 (cart _142062 _142064) s t). Qed.
Lemma lem8006722 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (@SUBSET (cart _142062 _142064) t t') = (term77 _142062 _142064 t t').
Proof. exact (@lem8006721 _142062 _142064 t t'). Qed.
Lemma lem8006752 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term80 _142062 _142063 _142064 s s' t t') = (term81 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8006689 _142062 _142063 s s') (@lem8006722 _142062 _142064 t t')). Qed.
Lemma lem8006813 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term82 _142062 _142063 _142064 s s' t t') = (term83 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8006646 _142062 _142064 t) (@lem8006752 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8006882 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term84 _142062 _142063 _142064 s s' t t') = (term85 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8006601 _142062 _142063 s) (@lem8006813 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8006959 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : ((term28 _142062 _142063 _142064 s t s' t') = (term84 _142062 _142063 _142064 s s' t t')) = ((term65 _142062 _142063 _142064 s t s' t') = (term85 _142062 _142063 _142064 s s' t t')).
Proof. exact (MK_COMB (@lem8006515 _142062 _142063 _142064 s t s' t') (@lem8006882 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8007087 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) : (term86 _142062 _142063 _142064 s s' t) = (term87 _142062 _142063 _142064 s s' t).
Proof. exact (fun_ext (fun t' : type24 _142062 _142064 => @lem8006959 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8007215 {_142062 _142064 : Type'} : (@all ((cart _142062 _142064) -> Prop)) = (@all ((cart _142062 _142064) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142062 _142064) -> Prop))). Qed.
Lemma lem8007216 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) : (term88 _142062 _142063 _142064 s s' t) = (term89 _142062 _142063 _142064 s s' t).
Proof. exact (MK_COMB (@lem8007215 _142062 _142064) (@lem8007087 _142062 _142063 _142064 s s' t)). Qed.
Lemma lem8007350 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) : (term90 _142062 _142063 _142064 s t) = (term91 _142062 _142063 _142064 s t).
Proof. exact (fun_ext (fun s' : type24 _142062 _142063 => @lem8007216 _142062 _142063 _142064 s s' t)). Qed.
Lemma lem8007484 {_142062 _142063 : Type'} : (@all ((cart _142062 _142063) -> Prop)) = (@all ((cart _142062 _142063) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142062 _142063) -> Prop))). Qed.
Lemma lem8007485 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) : (term92 _142062 _142063 _142064 s t) = (term93 _142062 _142063 _142064 s t).
Proof. exact (MK_COMB (@lem8007484 _142062 _142063) (@lem8007350 _142062 _142063 _142064 s t)). Qed.
Lemma lem8007625 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) : (term94 _142062 _142063 _142064 s) = (term95 _142062 _142063 _142064 s).
Proof. exact (fun_ext (fun t : type24 _142062 _142064 => @lem8007485 _142062 _142063 _142064 s t)). Qed.
Lemma lem8007765 {_142062 _142064 : Type'} : (@all ((cart _142062 _142064) -> Prop)) = (@all ((cart _142062 _142064) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142062 _142064) -> Prop))). Qed.
Lemma lem8007766 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) : (term96 _142062 _142063 _142064 s) = (term97 _142062 _142063 _142064 s).
Proof. exact (MK_COMB (@lem8007765 _142062 _142064) (@lem8007625 _142062 _142063 _142064 s)). Qed.
Lemma lem8007912 {_142062 _142063 _142064 : Type'} : (term98 _142062 _142063 _142064) = (term99 _142062 _142063 _142064).
Proof. exact (fun_ext (fun s : type24 _142062 _142063 => @lem8007766 _142062 _142063 _142064 s)). Qed.
Lemma lem8008058 {_142062 _142063 : Type'} : (@all ((cart _142062 _142063) -> Prop)) = (@all ((cart _142062 _142063) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142062 _142063) -> Prop))). Qed.
Lemma lem8008059 {_142062 _142063 _142064 : Type'} : (term100 _142062 _142063 _142064) = (term101 _142062 _142063 _142064).
Proof. exact (MK_COMB (@lem8008058 _142062 _142063) (@lem8007912 _142062 _142063 _142064)). Qed.
Lemma lem8008211 {_142062 _142063 _142064 : Type'} : (term101 _142062 _142063 _142064) = (term100 _142062 _142063 _142064).
Proof. exact (SYM (@lem8008059 _142062 _142063 _142064)). Qed.
Lemma lem8008213 (p : Prop) : p = (term102 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8008214 {_142062 _142063 _142064 : Type'} : (term101 _142062 _142063 _142064) = (term103 _142062 _142063 _142064).
Proof. exact (@lem8008213 (term101 _142062 _142063 _142064)). Qed.
Lemma lem8008215 {_142062 _142063 _142064 : Type'} : (term103 _142062 _142063 _142064) = (term101 _142062 _142063 _142064).
Proof. exact (SYM (@lem8008214 _142062 _142063 _142064)). Qed.
Lemma lem8008216 {_142062 _142063 _142064 : Type'} (h1 : term104 _142062 _142063 _142064) : term104 _142062 _142063 _142064.
Proof. exact (h1). Qed.
Lemma lem8008219 {_142062 _142063 _142064 : Type'} (h1 : term103 _142062 _142063 _142064) : term103 _142062 _142063 _142064.
Proof. exact (h1). Qed.
Lemma lem8008220 {_142062 _142063 _142064 : Type'} : term105 _142062 _142063 _142064.
Proof. exact (fun h0 : term103 _142062 _142063 _142064 => @lem8008219 _142062 _142063 _142064 h0). Qed.
Lemma lem8008221 {_142062 _142063 _142064 : Type'} (h1 : term105 _142062 _142063 _142064) : term105 _142062 _142063 _142064.
Proof. exact (h1). Qed.
Lemma lem8008222 {_142062 _142063 _142064 : Type'} (h1 : term103 _142062 _142063 _142064) : term103 _142062 _142063 _142064.
Proof. exact (h1). Qed.
Lemma lem8008223 {_142062 _142063 _142064 : Type'} (h1 : term103 _142062 _142063 _142064) (h2 : term105 _142062 _142063 _142064) : term103 _142062 _142063 _142064.
Proof. exact (@lem8008221 _142062 _142063 _142064 h2 (@lem8008222 _142062 _142063 _142064 h1)). Qed.
Lemma lem8008224 {_142062 _142063 _142064 : Type'} (h1 : term103 _142062 _142063 _142064) : term106 _142062 _142063 _142064.
Proof. exact (fun h0 : term105 _142062 _142063 _142064 => @lem8008223 _142062 _142063 _142064 h1 h0). Qed.
Lemma lem8008225 {_142062 _142063 _142064 : Type'} (h1 : term105 _142062 _142063 _142064) : term105 _142062 _142063 _142064.
Proof. exact (h1). Qed.
Lemma lem8008226 {_142062 _142063 _142064 : Type'} (h1 : term103 _142062 _142063 _142064) (h2 : term105 _142062 _142063 _142064) : term103 _142062 _142063 _142064.
Proof. exact (@lem8008224 _142062 _142063 _142064 h1 (@lem8008225 _142062 _142063 _142064 h2)). Qed.
Lemma lem8008227 {_142062 _142063 _142064 : Type'} (h1 : term105 _142062 _142063 _142064) : term105 _142062 _142063 _142064.
Proof. exact (fun h0 : term103 _142062 _142063 _142064 => @lem8008226 _142062 _142063 _142064 h0 h1). Qed.
Lemma lem8008228 {_142062 _142063 _142064 : Type'} : term107 _142062 _142063 _142064.
Proof. exact (fun h0 : term105 _142062 _142063 _142064 => @lem8008227 _142062 _142063 _142064 h0). Qed.
Lemma lem8008231 {_142062 _142063 _142064 : Type'} : term105 _142062 _142063 _142064.
Proof. exact (@lem8008228 _142062 _142063 _142064 (@lem8008220 _142062 _142063 _142064)). Qed.
Lemma lem8008232 {_142062 _142063 _142064 : Type'} : term105 _142062 _142063 _142064.
Proof. exact (@lem8008231 _142062 _142063 _142064). Qed.
Lemma lem8008234 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem8008235 {_142062 _142063 _142064 : Type'} : (term103 _142062 _142063 _142064) = (term108 _142062 _142063 _142064).
Proof. exact (@lem8008234 (term104 _142062 _142063 _142064)). Qed.
Lemma lem8008237 (t : Prop) : (term109 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem8008238 {_142062 _142063 _142064 : Type'} : (term108 _142062 _142063 _142064) = (term101 _142062 _142063 _142064).
Proof. exact (@lem8008237 (term101 _142062 _142063 _142064)). Qed.
Lemma lem8008299 {_142062 _142063 _142064 : Type'} : (term103 _142062 _142063 _142064) = (term101 _142062 _142063 _142064).
Proof. exact (TRANS (@lem8008235 _142062 _142063 _142064) (@lem8008238 _142062 _142063 _142064)). Qed.
Lemma lem8008304 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (x : cart _142062 _142064) (t' : type24 _142062 _142064) : (term110 _142062 _142064 t x t') = (term110 _142062 _142064 t x t').
Proof. exact (eq_refl (term110 _142062 _142064 t x t')). Qed.
Lemma lem8008305 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term111 _142062 _142064 t t') = (term111 _142062 _142064 t t').
Proof. exact (fun_ext (fun x : cart _142062 _142064 => @lem8008304 _142062 _142064 t x t')). Qed.
Lemma lem8008306 {_142062 _142064 : Type'} : (@all (cart _142062 _142064)) = (@all (cart _142062 _142064)).
Proof. exact (eq_refl (@all (cart _142062 _142064))). Qed.
Lemma lem8008307 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term77 _142062 _142064 t t') = (term77 _142062 _142064 t t').
Proof. exact (MK_COMB (@lem8008306 _142062 _142064) (@lem8008305 _142062 _142064 t t')). Qed.
Lemma lem8008312 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (x : cart _142062 _142063) (s' : type24 _142062 _142063) : (term110 _142062 _142063 s x s') = (term110 _142062 _142063 s x s').
Proof. exact (eq_refl (term110 _142062 _142063 s x s')). Qed.
Lemma lem8008313 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) : (term111 _142062 _142063 s s') = (term111 _142062 _142063 s s').
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8008312 _142062 _142063 s x s')). Qed.
Lemma lem8008314 {_142062 _142063 : Type'} : (@all (cart _142062 _142063)) = (@all (cart _142062 _142063)).
Proof. exact (eq_refl (@all (cart _142062 _142063))). Qed.
Lemma lem8008315 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) : (term77 _142062 _142063 s s') = (term77 _142062 _142063 s s').
Proof. exact (MK_COMB (@lem8008314 _142062 _142063) (@lem8008313 _142062 _142063 s s')). Qed.
Lemma lem8008316 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8008317 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) : (term79 _142062 _142063 s s') = (term79 _142062 _142063 s s').
Proof. exact (MK_COMB (@lem8008316) (@lem8008315 _142062 _142063 s s')). Qed.
Lemma lem8008318 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term81 _142062 _142063 _142064 s s' t t') = (term81 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8008317 _142062 _142063 s s') (@lem8008307 _142062 _142064 t t')). Qed.
Lemma lem8008321 {_142062 _142064 : Type'} (x : cart _142062 _142064) (t : type24 _142062 _142064) : (term71 _142062 _142064 x t) = (term71 _142062 _142064 x t).
Proof. exact (eq_refl (term71 _142062 _142064 x t)). Qed.
Lemma lem8008322 {_142062 _142064 : Type'} (t : type24 _142062 _142064) : (term73 _142062 _142064 t) = (term73 _142062 _142064 t).
Proof. exact (fun_ext (fun x : cart _142062 _142064 => @lem8008321 _142062 _142064 x t)). Qed.
Lemma lem8008323 {_142062 _142064 : Type'} : (@all (cart _142062 _142064)) = (@all (cart _142062 _142064)).
Proof. exact (eq_refl (@all (cart _142062 _142064))). Qed.
Lemma lem8008324 {_142062 _142064 : Type'} (t : type24 _142062 _142064) : (term74 _142062 _142064 t) = (term74 _142062 _142064 t).
Proof. exact (MK_COMB (@lem8008323 _142062 _142064) (@lem8008322 _142062 _142064 t)). Qed.
Lemma lem8008325 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8008326 {_142062 _142064 : Type'} (t : type24 _142062 _142064) : (term76 _142062 _142064 t) = (term76 _142062 _142064 t).
Proof. exact (MK_COMB (@lem8008325) (@lem8008324 _142062 _142064 t)). Qed.
Lemma lem8008327 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term83 _142062 _142063 _142064 s s' t t') = (term83 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8008326 _142062 _142064 t) (@lem8008318 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8008330 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) : (term71 _142062 _142063 x s) = (term71 _142062 _142063 x s).
Proof. exact (eq_refl (term71 _142062 _142063 x s)). Qed.
Lemma lem8008331 {_142062 _142063 : Type'} (s : type24 _142062 _142063) : (term73 _142062 _142063 s) = (term73 _142062 _142063 s).
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8008330 _142062 _142063 x s)). Qed.
Lemma lem8008332 {_142062 _142063 : Type'} : (@all (cart _142062 _142063)) = (@all (cart _142062 _142063)).
Proof. exact (eq_refl (@all (cart _142062 _142063))). Qed.
Lemma lem8008333 {_142062 _142063 : Type'} (s : type24 _142062 _142063) : (term74 _142062 _142063 s) = (term74 _142062 _142063 s).
Proof. exact (MK_COMB (@lem8008332 _142062 _142063) (@lem8008331 _142062 _142063 s)). Qed.
Lemma lem8008334 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8008335 {_142062 _142063 : Type'} (s : type24 _142062 _142063) : (term76 _142062 _142063 s) = (term76 _142062 _142063 s).
Proof. exact (MK_COMB (@lem8008334) (@lem8008333 _142062 _142063 s)). Qed.
Lemma lem8008336 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term85 _142062 _142063 _142064 s s' t t') = (term85 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8008335 _142062 _142063 s) (@lem8008327 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8008349 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (y : cart _142062 _142064) (t' : type24 _142062 _142064) : (term61 _142062 _142063 _142064 s t x s' y t') = (term61 _142062 _142063 _142064 s t x s' y t').
Proof. exact (eq_refl (term61 _142062 _142063 _142064 s t x s' y t')). Qed.
Lemma lem8008350 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term62 _142062 _142063 _142064 s t x s' t') = (term62 _142062 _142063 _142064 s t x s' t').
Proof. exact (fun_ext (fun y : cart _142062 _142064 => @lem8008349 _142062 _142063 _142064 s t x s' y t')). Qed.
Lemma lem8008351 {_142062 _142064 : Type'} : (@all (cart _142062 _142064)) = (@all (cart _142062 _142064)).
Proof. exact (eq_refl (@all (cart _142062 _142064))). Qed.
Lemma lem8008352 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term63 _142062 _142063 _142064 s t x s' t') = (term63 _142062 _142063 _142064 s t x s' t').
Proof. exact (MK_COMB (@lem8008351 _142062 _142064) (@lem8008350 _142062 _142063 _142064 s t x s' t')). Qed.
Lemma lem8008353 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term64 _142062 _142063 _142064 s t s' t') = (term64 _142062 _142063 _142064 s t s' t').
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8008352 _142062 _142063 _142064 s t x s' t')). Qed.
Lemma lem8008354 {_142062 _142063 : Type'} : (@all (cart _142062 _142063)) = (@all (cart _142062 _142063)).
Proof. exact (eq_refl (@all (cart _142062 _142063))). Qed.
Lemma lem8008355 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term65 _142062 _142063 _142064 s t s' t') = (term65 _142062 _142063 _142064 s t s' t').
Proof. exact (MK_COMB (@lem8008354 _142062 _142063) (@lem8008353 _142062 _142063 _142064 s t s' t')). Qed.
Lemma lem8008356 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8008357 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term67 _142062 _142063 _142064 s t s' t') = (term67 _142062 _142063 _142064 s t s' t').
Proof. exact (MK_COMB (@lem8008356) (@lem8008355 _142062 _142063 _142064 s t s' t')). Qed.
Lemma lem8008358 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : ((term65 _142062 _142063 _142064 s t s' t') = (term85 _142062 _142063 _142064 s s' t t')) = ((term65 _142062 _142063 _142064 s t s' t') = (term85 _142062 _142063 _142064 s s' t t')).
Proof. exact (MK_COMB (@lem8008357 _142062 _142063 _142064 s t s' t') (@lem8008336 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8008359 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) : (term87 _142062 _142063 _142064 s s' t) = (term87 _142062 _142063 _142064 s s' t).
Proof. exact (fun_ext (fun t' : type24 _142062 _142064 => @lem8008358 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8008360 {_142062 _142064 : Type'} : (@all ((cart _142062 _142064) -> Prop)) = (@all ((cart _142062 _142064) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142062 _142064) -> Prop))). Qed.
Lemma lem8008361 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) : (term89 _142062 _142063 _142064 s s' t) = (term89 _142062 _142063 _142064 s s' t).
Proof. exact (MK_COMB (@lem8008360 _142062 _142064) (@lem8008359 _142062 _142063 _142064 s s' t)). Qed.
Lemma lem8008362 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) : (term91 _142062 _142063 _142064 s t) = (term91 _142062 _142063 _142064 s t).
Proof. exact (fun_ext (fun s' : type24 _142062 _142063 => @lem8008361 _142062 _142063 _142064 s s' t)). Qed.
Lemma lem8008363 {_142062 _142063 : Type'} : (@all ((cart _142062 _142063) -> Prop)) = (@all ((cart _142062 _142063) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142062 _142063) -> Prop))). Qed.
Lemma lem8008364 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) : (term93 _142062 _142063 _142064 s t) = (term93 _142062 _142063 _142064 s t).
Proof. exact (MK_COMB (@lem8008363 _142062 _142063) (@lem8008362 _142062 _142063 _142064 s t)). Qed.
Lemma lem8008365 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) : (term95 _142062 _142063 _142064 s) = (term95 _142062 _142063 _142064 s).
Proof. exact (fun_ext (fun t : type24 _142062 _142064 => @lem8008364 _142062 _142063 _142064 s t)). Qed.
Lemma lem8008366 {_142062 _142064 : Type'} : (@all ((cart _142062 _142064) -> Prop)) = (@all ((cart _142062 _142064) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142062 _142064) -> Prop))). Qed.
Lemma lem8008367 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) : (term97 _142062 _142063 _142064 s) = (term97 _142062 _142063 _142064 s).
Proof. exact (MK_COMB (@lem8008366 _142062 _142064) (@lem8008365 _142062 _142063 _142064 s)). Qed.
Lemma lem8008368 {_142062 _142063 _142064 : Type'} : (term99 _142062 _142063 _142064) = (term99 _142062 _142063 _142064).
Proof. exact (fun_ext (fun s : type24 _142062 _142063 => @lem8008367 _142062 _142063 _142064 s)). Qed.
Lemma lem8008369 {_142062 _142063 : Type'} : (@all ((cart _142062 _142063) -> Prop)) = (@all ((cart _142062 _142063) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142062 _142063) -> Prop))). Qed.
Lemma lem8008370 {_142062 _142063 _142064 : Type'} : (term101 _142062 _142063 _142064) = (term101 _142062 _142063 _142064).
Proof. exact (MK_COMB (@lem8008369 _142062 _142063) (@lem8008368 _142062 _142063 _142064)). Qed.
Lemma lem8008449 {_142062 _142063 _142064 : Type'} : (term103 _142062 _142063 _142064) = (term101 _142062 _142063 _142064).
Proof. exact (TRANS (@lem8008299 _142062 _142063 _142064) (@lem8008370 _142062 _142063 _142064)). Qed.
Lemma lem8008450 {_142062 _142063 _142064 : Type'} : (term101 _142062 _142063 _142064) = (term103 _142062 _142063 _142064).
Proof. exact (SYM (@lem8008449 _142062 _142063 _142064)). Qed.
Lemma lem8008452 (p : Prop) : p = (term102 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8008453 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : ((term65 _142062 _142063 _142064 s t s' t') = (term85 _142062 _142063 _142064 s s' t t')) = (term112 _142062 _142063 _142064 s s' t t').
Proof. exact (@lem8008452 ((term65 _142062 _142063 _142064 s t s' t') = (term85 _142062 _142063 _142064 s s' t t'))). Qed.
Lemma lem8008454 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term112 _142062 _142063 _142064 s s' t t') = ((term65 _142062 _142063 _142064 s t s' t') = (term85 _142062 _142063 _142064 s s' t t')).
Proof. exact (SYM (@lem8008453 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8008455 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term113 _142062 _142063 _142064 s s' t t') : term113 _142062 _142063 _142064 s s' t t'.
Proof. exact (h1). Qed.
Lemma lem8008464 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (y : cart _142062 _142064) (t : type24 _142062 _142064) : (term114 _142062 _142063 _142064 x s y t) = (term115 _142062 _142063 _142064 x s y t).
Proof. exact (@lem17045 (@IN (cart _142062 _142063) x s) (@IN (cart _142062 _142064) y t)). Qed.
Lemma lem8008476 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s' : type24 _142062 _142063) (y : cart _142062 _142064) (t' : type24 _142062 _142064) : (term114 _142062 _142063 _142064 x s' y t') = (term115 _142062 _142063 _142064 x s' y t').
Proof. exact (@lem17045 (@IN (cart _142062 _142063) x s') (@IN (cart _142062 _142064) y t')). Qed.
Lemma lem8008479 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s' : type24 _142062 _142063) (y : cart _142062 _142064) (t' : type24 _142062 _142064) : (term18 _142062 _142063 _142064 x s' y t') = (term18 _142062 _142063 _142064 x s' y t').
Proof. exact (eq_refl (term18 _142062 _142063 _142064 x s' y t')). Qed.
Lemma lem8008481 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (y : cart _142062 _142064) (t : type24 _142062 _142064) : (term116 _142062 _142063 _142064 x s y t) = (term116 _142062 _142063 _142064 x s y t).
Proof. exact (eq_refl (term116 _142062 _142063 _142064 x s y t)). Qed.
Lemma lem8008482 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (y : cart _142062 _142064) (t' : type24 _142062 _142064) : (term117 _142062 _142063 _142064 s t x s' y t') = (term118 _142062 _142063 _142064 s t x s' y t').
Proof. exact (MK_COMB (@lem8008481 _142062 _142063 _142064 x s y t) (@lem8008476 _142062 _142063 _142064 x s' y t')). Qed.
Lemma lem8008483 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (y : cart _142062 _142064) (t' : type24 _142062 _142064) : (term119 _142062 _142063 _142064 s t x s' y t') = (term117 _142062 _142063 _142064 s t x s' y t').
Proof. exact (@lem17362 (term18 _142062 _142063 _142064 x s y t) (term18 _142062 _142063 _142064 x s' y t')). Qed.
Lemma lem8008484 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (y : cart _142062 _142064) (t' : type24 _142062 _142064) : (term119 _142062 _142063 _142064 s t x s' y t') = (term118 _142062 _142063 _142064 s t x s' y t').
Proof. exact (TRANS (@lem8008483 _142062 _142063 _142064 s t x s' y t') (@lem8008482 _142062 _142063 _142064 s t x s' y t')). Qed.
Lemma lem8008485 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8008486 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (y : cart _142062 _142064) (t : type24 _142062 _142064) : (term120 _142062 _142063 _142064 x s y t) = (term121 _142062 _142063 _142064 x s y t).
Proof. exact (MK_COMB (@lem8008485) (@lem8008464 _142062 _142063 _142064 x s y t)). Qed.
Lemma lem8008487 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (y : cart _142062 _142064) (t' : type24 _142062 _142064) : (term122 _142062 _142063 _142064 s t x s' y t') = (term123 _142062 _142063 _142064 s t x s' y t').
Proof. exact (MK_COMB (@lem8008486 _142062 _142063 _142064 x s y t) (@lem8008479 _142062 _142063 _142064 x s' y t')). Qed.
Lemma lem8008488 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (y : cart _142062 _142064) (t' : type24 _142062 _142064) : (term61 _142062 _142063 _142064 s t x s' y t') = (term122 _142062 _142063 _142064 s t x s' y t').
Proof. exact (@lem17265 (term18 _142062 _142063 _142064 x s y t) (term18 _142062 _142063 _142064 x s' y t')). Qed.
Lemma lem8008489 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (y : cart _142062 _142064) (t' : type24 _142062 _142064) : (term61 _142062 _142063 _142064 s t x s' y t') = (term123 _142062 _142063 _142064 s t x s' y t').
Proof. exact (TRANS (@lem8008488 _142062 _142063 _142064 s t x s' y t') (@lem8008487 _142062 _142063 _142064 s t x s' y t')). Qed.
Lemma lem8008490 {_142062 _142064 : Type'} (P : type24 _142062 _142064) : (term124 _142062 _142064 P) = (term125 _142062 _142064 P).
Proof. exact (@lem18392 (cart _142062 _142064) P). Qed.
Lemma lem8008491 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term126 _142062 _142063 _142064 s t x s' t') = (term127 _142062 _142063 _142064 s t x s' t').
Proof. exact (@lem8008490 _142062 _142064 (term62 _142062 _142063 _142064 s t x s' t')). Qed.
Lemma lem8008492 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (y : cart _142062 _142064) (t' : type24 _142062 _142064) : (term128 _142062 _142063 _142064 s t x s' t' y) = (term61 _142062 _142063 _142064 s t x s' y t').
Proof. exact (eq_refl (term128 _142062 _142063 _142064 s t x s' t' y)). Qed.
Lemma lem8008493 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8008494 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (y : cart _142062 _142064) (t' : type24 _142062 _142064) : (term129 _142062 _142063 _142064 s t x s' t' y) = (term119 _142062 _142063 _142064 s t x s' y t').
Proof. exact (MK_COMB (@lem8008493) (@lem8008492 _142062 _142063 _142064 s t x s' y t')). Qed.
Lemma lem8008495 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (y : cart _142062 _142064) (t' : type24 _142062 _142064) : (term129 _142062 _142063 _142064 s t x s' t' y) = (term118 _142062 _142063 _142064 s t x s' y t').
Proof. exact (TRANS (@lem8008494 _142062 _142063 _142064 s t x s' y t') (@lem8008484 _142062 _142063 _142064 s t x s' y t')). Qed.
Lemma lem8008496 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term130 _142062 _142063 _142064 s t x s' t') = (term131 _142062 _142063 _142064 s t x s' t').
Proof. exact (fun_ext (fun y : cart _142062 _142064 => @lem8008495 _142062 _142063 _142064 s t x s' y t')). Qed.
Lemma lem8008497 {_142062 _142064 : Type'} : (@ex (cart _142062 _142064)) = (@ex (cart _142062 _142064)).
Proof. exact (eq_refl (@ex (cart _142062 _142064))). Qed.
Lemma lem8008498 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term127 _142062 _142063 _142064 s t x s' t') = (term132 _142062 _142063 _142064 s t x s' t').
Proof. exact (MK_COMB (@lem8008497 _142062 _142064) (@lem8008496 _142062 _142063 _142064 s t x s' t')). Qed.
Lemma lem8008499 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term126 _142062 _142063 _142064 s t x s' t') = (term132 _142062 _142063 _142064 s t x s' t').
Proof. exact (TRANS (@lem8008491 _142062 _142063 _142064 s t x s' t') (@lem8008498 _142062 _142063 _142064 s t x s' t')). Qed.
Lemma lem8008500 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term62 _142062 _142063 _142064 s t x s' t') = (term133 _142062 _142063 _142064 s t x s' t').
Proof. exact (fun_ext (fun y : cart _142062 _142064 => @lem8008489 _142062 _142063 _142064 s t x s' y t')). Qed.
Lemma lem8008501 {_142062 _142064 : Type'} : (@all (cart _142062 _142064)) = (@all (cart _142062 _142064)).
Proof. exact (eq_refl (@all (cart _142062 _142064))). Qed.
Lemma lem8008502 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term63 _142062 _142063 _142064 s t x s' t') = (term134 _142062 _142063 _142064 s t x s' t').
Proof. exact (MK_COMB (@lem8008501 _142062 _142064) (@lem8008500 _142062 _142063 _142064 s t x s' t')). Qed.
Lemma lem8008503 {_142062 _142063 : Type'} (P : type24 _142062 _142063) : (term124 _142062 _142063 P) = (term125 _142062 _142063 P).
Proof. exact (@lem18392 (cart _142062 _142063) P). Qed.
Lemma lem8008504 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term135 _142062 _142063 _142064 s t s' t') = (term136 _142062 _142063 _142064 s t s' t').
Proof. exact (@lem8008503 _142062 _142063 (term64 _142062 _142063 _142064 s t s' t')). Qed.
Lemma lem8008505 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term137 _142062 _142063 _142064 s t s' t' x) = (term63 _142062 _142063 _142064 s t x s' t').
Proof. exact (eq_refl (term137 _142062 _142063 _142064 s t s' t' x)). Qed.
Lemma lem8008506 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8008507 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term138 _142062 _142063 _142064 s t s' t' x) = (term126 _142062 _142063 _142064 s t x s' t').
Proof. exact (MK_COMB (@lem8008506) (@lem8008505 _142062 _142063 _142064 s t x s' t')). Qed.
Lemma lem8008508 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term138 _142062 _142063 _142064 s t s' t' x) = (term132 _142062 _142063 _142064 s t x s' t').
Proof. exact (TRANS (@lem8008507 _142062 _142063 _142064 s t x s' t') (@lem8008499 _142062 _142063 _142064 s t x s' t')). Qed.
Lemma lem8008509 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term139 _142062 _142063 _142064 s t s' t') = (term140 _142062 _142063 _142064 s t s' t').
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8008508 _142062 _142063 _142064 s t x s' t')). Qed.
Lemma lem8008510 {_142062 _142063 : Type'} : (@ex (cart _142062 _142063)) = (@ex (cart _142062 _142063)).
Proof. exact (eq_refl (@ex (cart _142062 _142063))). Qed.
Lemma lem8008511 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term136 _142062 _142063 _142064 s t s' t') = (term141 _142062 _142063 _142064 s t s' t').
Proof. exact (MK_COMB (@lem8008510 _142062 _142063) (@lem8008509 _142062 _142063 _142064 s t s' t')). Qed.
Lemma lem8008512 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term135 _142062 _142063 _142064 s t s' t') = (term141 _142062 _142063 _142064 s t s' t').
Proof. exact (TRANS (@lem8008504 _142062 _142063 _142064 s t s' t') (@lem8008511 _142062 _142063 _142064 s t s' t')). Qed.
Lemma lem8008513 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term64 _142062 _142063 _142064 s t s' t') = (term142 _142062 _142063 _142064 s t s' t').
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8008502 _142062 _142063 _142064 s t x s' t')). Qed.
Lemma lem8008514 {_142062 _142063 : Type'} : (@all (cart _142062 _142063)) = (@all (cart _142062 _142063)).
Proof. exact (eq_refl (@all (cart _142062 _142063))). Qed.
Lemma lem8008515 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term65 _142062 _142063 _142064 s t s' t') = (term143 _142062 _142063 _142064 s t s' t').
Proof. exact (MK_COMB (@lem8008514 _142062 _142063) (@lem8008513 _142062 _142063 _142064 s t s' t')). Qed.
Lemma lem8008516 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) : (term71 _142062 _142063 x s) = (term71 _142062 _142063 x s).
Proof. exact (eq_refl (term71 _142062 _142063 x s)). Qed.
Lemma lem8008519 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) : (term144 _142062 _142063 x s) = (@IN (cart _142062 _142063) x s).
Proof. exact (@lem16933 (@IN (cart _142062 _142063) x s)). Qed.
Lemma lem8008520 {_142062 _142063 : Type'} (P : type24 _142062 _142063) : (term124 _142062 _142063 P) = (term125 _142062 _142063 P).
Proof. exact (@lem18392 (cart _142062 _142063) P). Qed.
Lemma lem8008521 {_142062 _142063 : Type'} (s : type24 _142062 _142063) : (term145 _142062 _142063 s) = (term146 _142062 _142063 s).
Proof. exact (@lem8008520 _142062 _142063 (term73 _142062 _142063 s)). Qed.
Lemma lem8008522 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) : (term147 _142062 _142063 s x) = (term71 _142062 _142063 x s).
Proof. exact (eq_refl (term147 _142062 _142063 s x)). Qed.
Lemma lem8008523 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8008524 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) : (term148 _142062 _142063 s x) = (term144 _142062 _142063 x s).
Proof. exact (MK_COMB (@lem8008523) (@lem8008522 _142062 _142063 x s)). Qed.
Lemma lem8008525 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) : (term148 _142062 _142063 s x) = (@IN (cart _142062 _142063) x s).
Proof. exact (TRANS (@lem8008524 _142062 _142063 x s) (@lem8008519 _142062 _142063 x s)). Qed.
Lemma lem8008526 {_142062 _142063 : Type'} (s : type24 _142062 _142063) : (term149 _142062 _142063 s) = (term150 _142062 _142063 s).
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8008525 _142062 _142063 x s)). Qed.
Lemma lem8008527 {_142062 _142063 : Type'} : (@ex (cart _142062 _142063)) = (@ex (cart _142062 _142063)).
Proof. exact (eq_refl (@ex (cart _142062 _142063))). Qed.
Lemma lem8008528 {_142062 _142063 : Type'} (s : type24 _142062 _142063) : (term146 _142062 _142063 s) = (term151 _142062 _142063 s).
Proof. exact (MK_COMB (@lem8008527 _142062 _142063) (@lem8008526 _142062 _142063 s)). Qed.
Lemma lem8008529 {_142062 _142063 : Type'} (s : type24 _142062 _142063) : (term145 _142062 _142063 s) = (term151 _142062 _142063 s).
Proof. exact (TRANS (@lem8008521 _142062 _142063 s) (@lem8008528 _142062 _142063 s)). Qed.
Lemma lem8008530 {_142062 _142063 : Type'} (s : type24 _142062 _142063) : (term73 _142062 _142063 s) = (term73 _142062 _142063 s).
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8008516 _142062 _142063 x s)). Qed.
Lemma lem8008531 {_142062 _142063 : Type'} : (@all (cart _142062 _142063)) = (@all (cart _142062 _142063)).
Proof. exact (eq_refl (@all (cart _142062 _142063))). Qed.
Lemma lem8008532 {_142062 _142063 : Type'} (s : type24 _142062 _142063) : (term74 _142062 _142063 s) = (term74 _142062 _142063 s).
Proof. exact (MK_COMB (@lem8008531 _142062 _142063) (@lem8008530 _142062 _142063 s)). Qed.
Lemma lem8008533 {_142062 _142064 : Type'} (x : cart _142062 _142064) (t : type24 _142062 _142064) : (term71 _142062 _142064 x t) = (term71 _142062 _142064 x t).
Proof. exact (eq_refl (term71 _142062 _142064 x t)). Qed.
Lemma lem8008536 {_142062 _142064 : Type'} (x : cart _142062 _142064) (t : type24 _142062 _142064) : (term144 _142062 _142064 x t) = (@IN (cart _142062 _142064) x t).
Proof. exact (@lem16933 (@IN (cart _142062 _142064) x t)). Qed.
Lemma lem8008537 {_142062 _142064 : Type'} (P : type24 _142062 _142064) : (term124 _142062 _142064 P) = (term125 _142062 _142064 P).
Proof. exact (@lem18392 (cart _142062 _142064) P). Qed.
Lemma lem8008538 {_142062 _142064 : Type'} (t : type24 _142062 _142064) : (term145 _142062 _142064 t) = (term146 _142062 _142064 t).
Proof. exact (@lem8008537 _142062 _142064 (term73 _142062 _142064 t)). Qed.
Lemma lem8008539 {_142062 _142064 : Type'} (x : cart _142062 _142064) (t : type24 _142062 _142064) : (term147 _142062 _142064 t x) = (term71 _142062 _142064 x t).
Proof. exact (eq_refl (term147 _142062 _142064 t x)). Qed.
Lemma lem8008540 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8008541 {_142062 _142064 : Type'} (x : cart _142062 _142064) (t : type24 _142062 _142064) : (term148 _142062 _142064 t x) = (term144 _142062 _142064 x t).
Proof. exact (MK_COMB (@lem8008540) (@lem8008539 _142062 _142064 x t)). Qed.
Lemma lem8008542 {_142062 _142064 : Type'} (x : cart _142062 _142064) (t : type24 _142062 _142064) : (term148 _142062 _142064 t x) = (@IN (cart _142062 _142064) x t).
Proof. exact (TRANS (@lem8008541 _142062 _142064 x t) (@lem8008536 _142062 _142064 x t)). Qed.
Lemma lem8008543 {_142062 _142064 : Type'} (t : type24 _142062 _142064) : (term149 _142062 _142064 t) = (term150 _142062 _142064 t).
Proof. exact (fun_ext (fun x : cart _142062 _142064 => @lem8008542 _142062 _142064 x t)). Qed.
Lemma lem8008544 {_142062 _142064 : Type'} : (@ex (cart _142062 _142064)) = (@ex (cart _142062 _142064)).
Proof. exact (eq_refl (@ex (cart _142062 _142064))). Qed.
Lemma lem8008545 {_142062 _142064 : Type'} (t : type24 _142062 _142064) : (term146 _142062 _142064 t) = (term151 _142062 _142064 t).
Proof. exact (MK_COMB (@lem8008544 _142062 _142064) (@lem8008543 _142062 _142064 t)). Qed.
Lemma lem8008546 {_142062 _142064 : Type'} (t : type24 _142062 _142064) : (term145 _142062 _142064 t) = (term151 _142062 _142064 t).
Proof. exact (TRANS (@lem8008538 _142062 _142064 t) (@lem8008545 _142062 _142064 t)). Qed.
Lemma lem8008547 {_142062 _142064 : Type'} (t : type24 _142062 _142064) : (term73 _142062 _142064 t) = (term73 _142062 _142064 t).
Proof. exact (fun_ext (fun x : cart _142062 _142064 => @lem8008533 _142062 _142064 x t)). Qed.
Lemma lem8008548 {_142062 _142064 : Type'} : (@all (cart _142062 _142064)) = (@all (cart _142062 _142064)).
Proof. exact (eq_refl (@all (cart _142062 _142064))). Qed.
Lemma lem8008549 {_142062 _142064 : Type'} (t : type24 _142062 _142064) : (term74 _142062 _142064 t) = (term74 _142062 _142064 t).
Proof. exact (MK_COMB (@lem8008548 _142062 _142064) (@lem8008547 _142062 _142064 t)). Qed.
Lemma lem8008558 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (x : cart _142062 _142063) (s' : type24 _142062 _142063) : (term152 _142062 _142063 s x s') = (term153 _142062 _142063 s x s').
Proof. exact (@lem17362 (@IN (cart _142062 _142063) x s) (@IN (cart _142062 _142063) x s')). Qed.
Lemma lem8008563 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (x : cart _142062 _142063) (s' : type24 _142062 _142063) : (term110 _142062 _142063 s x s') = (term154 _142062 _142063 s x s').
Proof. exact (@lem17265 (@IN (cart _142062 _142063) x s) (@IN (cart _142062 _142063) x s')). Qed.
Lemma lem8008564 {_142062 _142063 : Type'} (P : type24 _142062 _142063) : (term124 _142062 _142063 P) = (term125 _142062 _142063 P).
Proof. exact (@lem18392 (cart _142062 _142063) P). Qed.
Lemma lem8008565 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) : (term155 _142062 _142063 s s') = (term156 _142062 _142063 s s').
Proof. exact (@lem8008564 _142062 _142063 (term111 _142062 _142063 s s')). Qed.
Lemma lem8008566 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (x : cart _142062 _142063) (s' : type24 _142062 _142063) : (term157 _142062 _142063 s s' x) = (term110 _142062 _142063 s x s').
Proof. exact (eq_refl (term157 _142062 _142063 s s' x)). Qed.
Lemma lem8008567 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8008568 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (x : cart _142062 _142063) (s' : type24 _142062 _142063) : (term158 _142062 _142063 s s' x) = (term152 _142062 _142063 s x s').
Proof. exact (MK_COMB (@lem8008567) (@lem8008566 _142062 _142063 s x s')). Qed.
Lemma lem8008569 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (x : cart _142062 _142063) (s' : type24 _142062 _142063) : (term158 _142062 _142063 s s' x) = (term153 _142062 _142063 s x s').
Proof. exact (TRANS (@lem8008568 _142062 _142063 s x s') (@lem8008558 _142062 _142063 s x s')). Qed.
Lemma lem8008570 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) : (term159 _142062 _142063 s s') = (term160 _142062 _142063 s s').
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8008569 _142062 _142063 s x s')). Qed.
Lemma lem8008571 {_142062 _142063 : Type'} : (@ex (cart _142062 _142063)) = (@ex (cart _142062 _142063)).
Proof. exact (eq_refl (@ex (cart _142062 _142063))). Qed.
Lemma lem8008572 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) : (term156 _142062 _142063 s s') = (term161 _142062 _142063 s s').
Proof. exact (MK_COMB (@lem8008571 _142062 _142063) (@lem8008570 _142062 _142063 s s')). Qed.
Lemma lem8008573 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) : (term155 _142062 _142063 s s') = (term161 _142062 _142063 s s').
Proof. exact (TRANS (@lem8008565 _142062 _142063 s s') (@lem8008572 _142062 _142063 s s')). Qed.
Lemma lem8008574 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) : (term111 _142062 _142063 s s') = (term162 _142062 _142063 s s').
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8008563 _142062 _142063 s x s')). Qed.
Lemma lem8008575 {_142062 _142063 : Type'} : (@all (cart _142062 _142063)) = (@all (cart _142062 _142063)).
Proof. exact (eq_refl (@all (cart _142062 _142063))). Qed.
Lemma lem8008576 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) : (term77 _142062 _142063 s s') = (term163 _142062 _142063 s s').
Proof. exact (MK_COMB (@lem8008575 _142062 _142063) (@lem8008574 _142062 _142063 s s')). Qed.
Lemma lem8008585 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (x : cart _142062 _142064) (t' : type24 _142062 _142064) : (term152 _142062 _142064 t x t') = (term153 _142062 _142064 t x t').
Proof. exact (@lem17362 (@IN (cart _142062 _142064) x t) (@IN (cart _142062 _142064) x t')). Qed.
Lemma lem8008590 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (x : cart _142062 _142064) (t' : type24 _142062 _142064) : (term110 _142062 _142064 t x t') = (term154 _142062 _142064 t x t').
Proof. exact (@lem17265 (@IN (cart _142062 _142064) x t) (@IN (cart _142062 _142064) x t')). Qed.
Lemma lem8008591 {_142062 _142064 : Type'} (P : type24 _142062 _142064) : (term124 _142062 _142064 P) = (term125 _142062 _142064 P).
Proof. exact (@lem18392 (cart _142062 _142064) P). Qed.
Lemma lem8008592 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term155 _142062 _142064 t t') = (term156 _142062 _142064 t t').
Proof. exact (@lem8008591 _142062 _142064 (term111 _142062 _142064 t t')). Qed.
Lemma lem8008593 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (x : cart _142062 _142064) (t' : type24 _142062 _142064) : (term157 _142062 _142064 t t' x) = (term110 _142062 _142064 t x t').
Proof. exact (eq_refl (term157 _142062 _142064 t t' x)). Qed.
Lemma lem8008594 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8008595 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (x : cart _142062 _142064) (t' : type24 _142062 _142064) : (term158 _142062 _142064 t t' x) = (term152 _142062 _142064 t x t').
Proof. exact (MK_COMB (@lem8008594) (@lem8008593 _142062 _142064 t x t')). Qed.
Lemma lem8008596 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (x : cart _142062 _142064) (t' : type24 _142062 _142064) : (term158 _142062 _142064 t t' x) = (term153 _142062 _142064 t x t').
Proof. exact (TRANS (@lem8008595 _142062 _142064 t x t') (@lem8008585 _142062 _142064 t x t')). Qed.
Lemma lem8008597 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term159 _142062 _142064 t t') = (term160 _142062 _142064 t t').
Proof. exact (fun_ext (fun x : cart _142062 _142064 => @lem8008596 _142062 _142064 t x t')). Qed.
Lemma lem8008598 {_142062 _142064 : Type'} : (@ex (cart _142062 _142064)) = (@ex (cart _142062 _142064)).
Proof. exact (eq_refl (@ex (cart _142062 _142064))). Qed.
Lemma lem8008599 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term156 _142062 _142064 t t') = (term161 _142062 _142064 t t').
Proof. exact (MK_COMB (@lem8008598 _142062 _142064) (@lem8008597 _142062 _142064 t t')). Qed.
Lemma lem8008600 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term155 _142062 _142064 t t') = (term161 _142062 _142064 t t').
Proof. exact (TRANS (@lem8008592 _142062 _142064 t t') (@lem8008599 _142062 _142064 t t')). Qed.
Lemma lem8008601 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term111 _142062 _142064 t t') = (term162 _142062 _142064 t t').
Proof. exact (fun_ext (fun x : cart _142062 _142064 => @lem8008590 _142062 _142064 t x t')). Qed.
Lemma lem8008602 {_142062 _142064 : Type'} : (@all (cart _142062 _142064)) = (@all (cart _142062 _142064)).
Proof. exact (eq_refl (@all (cart _142062 _142064))). Qed.
Lemma lem8008603 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term77 _142062 _142064 t t') = (term163 _142062 _142064 t t').
Proof. exact (MK_COMB (@lem8008602 _142062 _142064) (@lem8008601 _142062 _142064 t t')). Qed.
Lemma lem8008604 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8008605 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) : (term164 _142062 _142063 s s') = (term165 _142062 _142063 s s').
Proof. exact (MK_COMB (@lem8008604) (@lem8008573 _142062 _142063 s s')). Qed.
Lemma lem8008606 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term166 _142062 _142063 _142064 s s' t t') = (term167 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8008605 _142062 _142063 s s') (@lem8008600 _142062 _142064 t t')). Qed.
Lemma lem8008607 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term168 _142062 _142063 _142064 s s' t t') = (term166 _142062 _142063 _142064 s s' t t').
Proof. exact (@lem17045 (term77 _142062 _142063 s s') (term77 _142062 _142064 t t')). Qed.
Lemma lem8008608 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term168 _142062 _142063 _142064 s s' t t') = (term167 _142062 _142063 _142064 s s' t t').
Proof. exact (TRANS (@lem8008607 _142062 _142063 _142064 s s' t t') (@lem8008606 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8008609 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8008610 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) : (term79 _142062 _142063 s s') = (term169 _142062 _142063 s s').
Proof. exact (MK_COMB (@lem8008609) (@lem8008576 _142062 _142063 s s')). Qed.
Lemma lem8008611 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term81 _142062 _142063 _142064 s s' t t') = (term170 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8008610 _142062 _142063 s s') (@lem8008603 _142062 _142064 t t')). Qed.
Lemma lem8008612 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8008613 {_142062 _142064 : Type'} (t : type24 _142062 _142064) : (term171 _142062 _142064 t) = (term172 _142062 _142064 t).
Proof. exact (MK_COMB (@lem8008612) (@lem8008546 _142062 _142064 t)). Qed.
Lemma lem8008614 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term173 _142062 _142063 _142064 s s' t t') = (term174 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8008613 _142062 _142064 t) (@lem8008608 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8008615 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term175 _142062 _142063 _142064 s s' t t') = (term173 _142062 _142063 _142064 s s' t t').
Proof. exact (@lem17160 (term74 _142062 _142064 t) (term81 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8008616 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term175 _142062 _142063 _142064 s s' t t') = (term174 _142062 _142063 _142064 s s' t t').
Proof. exact (TRANS (@lem8008615 _142062 _142063 _142064 s s' t t') (@lem8008614 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8008617 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8008618 {_142062 _142064 : Type'} (t : type24 _142062 _142064) : (term76 _142062 _142064 t) = (term76 _142062 _142064 t).
Proof. exact (MK_COMB (@lem8008617) (@lem8008549 _142062 _142064 t)). Qed.
Lemma lem8008619 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term83 _142062 _142063 _142064 s s' t t') = (term176 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8008618 _142062 _142064 t) (@lem8008611 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8008620 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8008621 {_142062 _142063 : Type'} (s : type24 _142062 _142063) : (term171 _142062 _142063 s) = (term172 _142062 _142063 s).
Proof. exact (MK_COMB (@lem8008620) (@lem8008529 _142062 _142063 s)). Qed.
Lemma lem8008622 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term177 _142062 _142063 _142064 s s' t t') = (term178 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8008621 _142062 _142063 s) (@lem8008616 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8008623 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term179 _142062 _142063 _142064 s s' t t') = (term177 _142062 _142063 _142064 s s' t t').
Proof. exact (@lem17160 (term74 _142062 _142063 s) (term83 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8008624 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term179 _142062 _142063 _142064 s s' t t') = (term178 _142062 _142063 _142064 s s' t t').
Proof. exact (TRANS (@lem8008623 _142062 _142063 _142064 s s' t t') (@lem8008622 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8008625 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8008626 {_142062 _142063 : Type'} (s : type24 _142062 _142063) : (term76 _142062 _142063 s) = (term76 _142062 _142063 s).
Proof. exact (MK_COMB (@lem8008625) (@lem8008532 _142062 _142063 s)). Qed.
Lemma lem8008627 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term85 _142062 _142063 _142064 s s' t t') = (term180 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8008626 _142062 _142063 s) (@lem8008619 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8008628 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8008629 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term181 _142062 _142063 _142064 s t s' t') = (term182 _142062 _142063 _142064 s t s' t').
Proof. exact (MK_COMB (@lem8008628) (@lem8008512 _142062 _142063 _142064 s t s' t')). Qed.
Lemma lem8008630 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term183 _142062 _142063 _142064 s s' t t') = (term184 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8008629 _142062 _142063 _142064 s t s' t') (@lem8008627 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8008631 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8008632 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term185 _142062 _142063 _142064 s t s' t') = (term186 _142062 _142063 _142064 s t s' t').
Proof. exact (MK_COMB (@lem8008631) (@lem8008515 _142062 _142063 _142064 s t s' t')). Qed.
Lemma lem8008633 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term187 _142062 _142063 _142064 s s' t t') = (term188 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8008632 _142062 _142063 _142064 s t s' t') (@lem8008624 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8008634 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8008635 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term189 _142062 _142063 _142064 s s' t t') = (term190 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8008634) (@lem8008633 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8008636 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term191 _142062 _142063 _142064 s s' t t') = (term192 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8008635 _142062 _142063 _142064 s s' t t') (@lem8008630 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8008637 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term113 _142062 _142063 _142064 s s' t t') = (term191 _142062 _142063 _142064 s s' t t').
Proof. exact (@lem17646 (term65 _142062 _142063 _142064 s t s' t') (term85 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8008638 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term113 _142062 _142063 _142064 s s' t t') = (term192 _142062 _142063 _142064 s s' t t').
Proof. exact (TRANS (@lem8008637 _142062 _142063 _142064 s s' t t') (@lem8008636 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8008955 {A : Type'} (P : A -> Prop) (Q : Prop) : (term193 A P Q) = (term194 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem8008956 {_142062 _142063 : Type'} (P : type24 _142062 _142063) (Q : Prop) : (term195 _142062 _142063 P Q) = (term196 _142062 _142063 P Q).
Proof. exact (@lem8008955 (cart _142062 _142063) P Q). Qed.
Lemma lem8008957 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term197 _142062 _142063 _142064 s s' t t') = (term198 _142062 _142063 _142064 s s' t t').
Proof. exact (@lem8008956 _142062 _142063 (term160 _142062 _142063 s s') (term161 _142062 _142064 t t')). Qed.
Lemma lem8008958 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (x : cart _142062 _142063) (s' : type24 _142062 _142063) : (term199 _142062 _142063 s s' x) = (term153 _142062 _142063 s x s').
Proof. exact (eq_refl (term199 _142062 _142063 s s' x)). Qed.
Lemma lem8008959 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) : (term200 _142062 _142063 s s') = (term160 _142062 _142063 s s').
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8008958 _142062 _142063 s x s')). Qed.
Lemma lem8008960 {_142062 _142063 : Type'} : (@ex (cart _142062 _142063)) = (@ex (cart _142062 _142063)).
Proof. exact (eq_refl (@ex (cart _142062 _142063))). Qed.
Lemma lem8008961 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) : (term201 _142062 _142063 s s') = (term161 _142062 _142063 s s').
Proof. exact (MK_COMB (@lem8008960 _142062 _142063) (@lem8008959 _142062 _142063 s s')). Qed.
Lemma lem8008962 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8008963 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) : (term202 _142062 _142063 s s') = (term165 _142062 _142063 s s').
Proof. exact (MK_COMB (@lem8008962) (@lem8008961 _142062 _142063 s s')). Qed.
Lemma lem8008964 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term161 _142062 _142064 t t') = (term161 _142062 _142064 t t').
Proof. exact (eq_refl (term161 _142062 _142064 t t')). Qed.
Lemma lem8008965 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term197 _142062 _142063 _142064 s s' t t') = (term167 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8008963 _142062 _142063 s s') (@lem8008964 _142062 _142064 t t')). Qed.
Lemma lem8008966 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8008967 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term203 _142062 _142063 _142064 s s' t t') = (term204 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8008966) (@lem8008965 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8008968 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (x : cart _142062 _142063) (s' : type24 _142062 _142063) : (term199 _142062 _142063 s s' x) = (term153 _142062 _142063 s x s').
Proof. exact (eq_refl (term199 _142062 _142063 s s' x)). Qed.
Lemma lem8008969 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8008970 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (x : cart _142062 _142063) (s' : type24 _142062 _142063) : (term205 _142062 _142063 s s' x) = (term206 _142062 _142063 s x s').
Proof. exact (MK_COMB (@lem8008969) (@lem8008968 _142062 _142063 s x s')). Qed.
Lemma lem8008971 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term161 _142062 _142064 t t') = (term161 _142062 _142064 t t').
Proof. exact (eq_refl (term161 _142062 _142064 t t')). Qed.
Lemma lem8008972 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term207 _142062 _142063 _142064 s s' x t t') = (term208 _142062 _142063 _142064 s x s' t t').
Proof. exact (MK_COMB (@lem8008970 _142062 _142063 s x s') (@lem8008971 _142062 _142064 t t')). Qed.
Lemma lem8008973 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term209 _142062 _142063 _142064 s s' t t') = (term210 _142062 _142063 _142064 s s' t t').
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8008972 _142062 _142063 _142064 s x s' t t')). Qed.
Lemma lem8008974 {_142062 _142063 : Type'} : (@ex (cart _142062 _142063)) = (@ex (cart _142062 _142063)).
Proof. exact (eq_refl (@ex (cart _142062 _142063))). Qed.
Lemma lem8008975 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term198 _142062 _142063 _142064 s s' t t') = (term211 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8008974 _142062 _142063) (@lem8008973 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8008976 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : ((term197 _142062 _142063 _142064 s s' t t') = (term198 _142062 _142063 _142064 s s' t t')) = ((term167 _142062 _142063 _142064 s s' t t') = (term211 _142062 _142063 _142064 s s' t t')).
Proof. exact (MK_COMB (@lem8008967 _142062 _142063 _142064 s s' t t') (@lem8008975 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8008977 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term167 _142062 _142063 _142064 s s' t t') = (term211 _142062 _142063 _142064 s s' t t').
Proof. exact (EQ_MP (@lem8008976 _142062 _142063 _142064 s s' t t') (@lem8008957 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8008979 {A : Type'} (P : Prop) (Q : A -> Prop) : (term212 A P Q) = (term213 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem8008980 {_142062 _142064 : Type'} (P : Prop) (Q : type24 _142062 _142064) : (term214 _142062 _142064 P Q) = (term215 _142062 _142064 P Q).
Proof. exact (@lem8008979 (cart _142062 _142064) P Q). Qed.
Lemma lem8008981 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term216 _142062 _142063 _142064 s x s' t t') = (term217 _142062 _142063 _142064 s x s' t t').
Proof. exact (@lem8008980 _142062 _142064 (term153 _142062 _142063 s x s') (term160 _142062 _142064 t t')). Qed.
Lemma lem8008982 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (x : cart _142062 _142064) (t' : type24 _142062 _142064) : (term199 _142062 _142064 t t' x) = (term153 _142062 _142064 t x t').
Proof. exact (eq_refl (term199 _142062 _142064 t t' x)). Qed.
Lemma lem8008983 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term200 _142062 _142064 t t') = (term160 _142062 _142064 t t').
Proof. exact (fun_ext (fun x : cart _142062 _142064 => @lem8008982 _142062 _142064 t x t')). Qed.
Lemma lem8008984 {_142062 _142064 : Type'} : (@ex (cart _142062 _142064)) = (@ex (cart _142062 _142064)).
Proof. exact (eq_refl (@ex (cart _142062 _142064))). Qed.
Lemma lem8008985 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term201 _142062 _142064 t t') = (term161 _142062 _142064 t t').
Proof. exact (MK_COMB (@lem8008984 _142062 _142064) (@lem8008983 _142062 _142064 t t')). Qed.
Lemma lem8008986 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (x : cart _142062 _142063) (s' : type24 _142062 _142063) : (term206 _142062 _142063 s x s') = (term206 _142062 _142063 s x s').
Proof. exact (eq_refl (term206 _142062 _142063 s x s')). Qed.
Lemma lem8008987 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term216 _142062 _142063 _142064 s x s' t t') = (term208 _142062 _142063 _142064 s x s' t t').
Proof. exact (MK_COMB (@lem8008986 _142062 _142063 s x s') (@lem8008985 _142062 _142064 t t')). Qed.
Lemma lem8008988 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8008989 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term218 _142062 _142063 _142064 s x s' t t') = (term219 _142062 _142063 _142064 s x s' t t').
Proof. exact (MK_COMB (@lem8008988) (@lem8008987 _142062 _142063 _142064 s x s' t t')). Qed.
Lemma lem8008990 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (x : cart _142062 _142064) (t' : type24 _142062 _142064) : (term199 _142062 _142064 t t' x) = (term153 _142062 _142064 t x t').
Proof. exact (eq_refl (term199 _142062 _142064 t t' x)). Qed.
Lemma lem8008991 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (x : cart _142062 _142063) (s' : type24 _142062 _142063) : (term206 _142062 _142063 s x s') = (term206 _142062 _142063 s x s').
Proof. exact (eq_refl (term206 _142062 _142063 s x s')). Qed.
Lemma lem8008992 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x' : cart _142062 _142064) (t' : type24 _142062 _142064) : (term220 _142062 _142063 _142064 s x s' t t' x') = (term221 _142062 _142063 _142064 s x s' t x' t').
Proof. exact (MK_COMB (@lem8008991 _142062 _142063 s x s') (@lem8008990 _142062 _142064 t x' t')). Qed.
Lemma lem8008993 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term222 _142062 _142063 _142064 s x s' t t') = (term223 _142062 _142063 _142064 s x s' t t').
Proof. exact (fun_ext (fun x' : cart _142062 _142064 => @lem8008992 _142062 _142063 _142064 s x s' t x' t')). Qed.
Lemma lem8008994 {_142062 _142064 : Type'} : (@ex (cart _142062 _142064)) = (@ex (cart _142062 _142064)).
Proof. exact (eq_refl (@ex (cart _142062 _142064))). Qed.
Lemma lem8008995 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term217 _142062 _142063 _142064 s x s' t t') = (term224 _142062 _142063 _142064 s x s' t t').
Proof. exact (MK_COMB (@lem8008994 _142062 _142064) (@lem8008993 _142062 _142063 _142064 s x s' t t')). Qed.
Lemma lem8008996 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : ((term216 _142062 _142063 _142064 s x s' t t') = (term217 _142062 _142063 _142064 s x s' t t')) = ((term208 _142062 _142063 _142064 s x s' t t') = (term224 _142062 _142063 _142064 s x s' t t')).
Proof. exact (MK_COMB (@lem8008989 _142062 _142063 _142064 s x s' t t') (@lem8008995 _142062 _142063 _142064 s x s' t t')). Qed.
Lemma lem8008997 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term208 _142062 _142063 _142064 s x s' t t') = (term224 _142062 _142063 _142064 s x s' t t').
Proof. exact (EQ_MP (@lem8008996 _142062 _142063 _142064 s x s' t t') (@lem8008981 _142062 _142063 _142064 s x s' t t')). Qed.
Lemma lem8008998 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term210 _142062 _142063 _142064 s s' t t') = (term225 _142062 _142063 _142064 s s' t t').
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8008997 _142062 _142063 _142064 s x s' t t')). Qed.
Lemma lem8008999 {_142062 _142063 : Type'} : (@ex (cart _142062 _142063)) = (@ex (cart _142062 _142063)).
Proof. exact (eq_refl (@ex (cart _142062 _142063))). Qed.
Lemma lem8009000 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term211 _142062 _142063 _142064 s s' t t') = (term226 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8008999 _142062 _142063) (@lem8008998 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009001 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term167 _142062 _142063 _142064 s s' t t') = (term226 _142062 _142063 _142064 s s' t t').
Proof. exact (TRANS (@lem8008977 _142062 _142063 _142064 s s' t t') (@lem8009000 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009002 {_142062 _142064 : Type'} (t : type24 _142062 _142064) : (term172 _142062 _142064 t) = (term172 _142062 _142064 t).
Proof. exact (eq_refl (term172 _142062 _142064 t)). Qed.
Lemma lem8009003 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term174 _142062 _142063 _142064 s s' t t') = (term227 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009002 _142062 _142064 t) (@lem8009001 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009005 {A : Type'} (P : A -> Prop) (Q : Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem8009006 {_142062 _142064 : Type'} (P : type24 _142062 _142064) (Q : Prop) : (term230 _142062 _142064 P Q) = (term231 _142062 _142064 P Q).
Proof. exact (@lem8009005 (cart _142062 _142064) P Q). Qed.
Lemma lem8009007 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term232 _142062 _142063 _142064 s s' t t') = (term233 _142062 _142063 _142064 s s' t t').
Proof. exact (@lem8009006 _142062 _142064 (term150 _142062 _142064 t) (term226 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009008 {_142062 _142064 : Type'} (x : cart _142062 _142064) (t : type24 _142062 _142064) : (term234 _142062 _142064 t x) = (@IN (cart _142062 _142064) x t).
Proof. exact (eq_refl (term234 _142062 _142064 t x)). Qed.
Lemma lem8009009 {_142062 _142064 : Type'} (t : type24 _142062 _142064) : (term235 _142062 _142064 t) = (term150 _142062 _142064 t).
Proof. exact (fun_ext (fun x : cart _142062 _142064 => @lem8009008 _142062 _142064 x t)). Qed.
Lemma lem8009010 {_142062 _142064 : Type'} : (@ex (cart _142062 _142064)) = (@ex (cart _142062 _142064)).
Proof. exact (eq_refl (@ex (cart _142062 _142064))). Qed.
Lemma lem8009011 {_142062 _142064 : Type'} (t : type24 _142062 _142064) : (term236 _142062 _142064 t) = (term151 _142062 _142064 t).
Proof. exact (MK_COMB (@lem8009010 _142062 _142064) (@lem8009009 _142062 _142064 t)). Qed.
Lemma lem8009012 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8009013 {_142062 _142064 : Type'} (t : type24 _142062 _142064) : (term237 _142062 _142064 t) = (term172 _142062 _142064 t).
Proof. exact (MK_COMB (@lem8009012) (@lem8009011 _142062 _142064 t)). Qed.
Lemma lem8009014 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term226 _142062 _142063 _142064 s s' t t') = (term226 _142062 _142063 _142064 s s' t t').
Proof. exact (eq_refl (term226 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009015 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term232 _142062 _142063 _142064 s s' t t') = (term227 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009013 _142062 _142064 t) (@lem8009014 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009016 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8009017 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term238 _142062 _142063 _142064 s s' t t') = (term239 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009016) (@lem8009015 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009018 {_142062 _142064 : Type'} (x : cart _142062 _142064) (t : type24 _142062 _142064) : (term234 _142062 _142064 t x) = (@IN (cart _142062 _142064) x t).
Proof. exact (eq_refl (term234 _142062 _142064 t x)). Qed.
Lemma lem8009019 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8009020 {_142062 _142064 : Type'} (x : cart _142062 _142064) (t : type24 _142062 _142064) : (term240 _142062 _142064 t x) = (term241 _142062 _142064 x t).
Proof. exact (MK_COMB (@lem8009019) (@lem8009018 _142062 _142064 x t)). Qed.
Lemma lem8009021 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term226 _142062 _142063 _142064 s s' t t') = (term226 _142062 _142063 _142064 s s' t t').
Proof. exact (eq_refl (term226 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009022 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term242 _142062 _142063 _142064 x s s' t t') = (term243 _142062 _142063 _142064 x s s' t t').
Proof. exact (MK_COMB (@lem8009020 _142062 _142064 x t) (@lem8009021 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009023 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term244 _142062 _142063 _142064 s s' t t') = (term245 _142062 _142063 _142064 s s' t t').
Proof. exact (fun_ext (fun x : cart _142062 _142064 => @lem8009022 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009024 {_142062 _142064 : Type'} : (@ex (cart _142062 _142064)) = (@ex (cart _142062 _142064)).
Proof. exact (eq_refl (@ex (cart _142062 _142064))). Qed.
Lemma lem8009025 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term233 _142062 _142063 _142064 s s' t t') = (term246 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009024 _142062 _142064) (@lem8009023 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009026 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : ((term232 _142062 _142063 _142064 s s' t t') = (term233 _142062 _142063 _142064 s s' t t')) = ((term227 _142062 _142063 _142064 s s' t t') = (term246 _142062 _142063 _142064 s s' t t')).
Proof. exact (MK_COMB (@lem8009017 _142062 _142063 _142064 s s' t t') (@lem8009025 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009027 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term227 _142062 _142063 _142064 s s' t t') = (term246 _142062 _142063 _142064 s s' t t').
Proof. exact (EQ_MP (@lem8009026 _142062 _142063 _142064 s s' t t') (@lem8009007 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009029 {A : Type'} (P : Prop) (Q : A -> Prop) : (term247 A P Q) = (term248 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8009030 {_142062 _142063 : Type'} (P : Prop) (Q : type24 _142062 _142063) : (term249 _142062 _142063 P Q) = (term250 _142062 _142063 P Q).
Proof. exact (@lem8009029 (cart _142062 _142063) P Q). Qed.
Lemma lem8009031 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term251 _142062 _142063 _142064 x s s' t t') = (term252 _142062 _142063 _142064 x s s' t t').
Proof. exact (@lem8009030 _142062 _142063 (@IN (cart _142062 _142064) x t) (term225 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009032 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term253 _142062 _142063 _142064 s s' t t' x) = (term224 _142062 _142063 _142064 s x s' t t').
Proof. exact (eq_refl (term253 _142062 _142063 _142064 s s' t t' x)). Qed.
Lemma lem8009033 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term254 _142062 _142063 _142064 s s' t t') = (term225 _142062 _142063 _142064 s s' t t').
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8009032 _142062 _142063 _142064 s x s' t t')). Qed.
Lemma lem8009034 {_142062 _142063 : Type'} : (@ex (cart _142062 _142063)) = (@ex (cart _142062 _142063)).
Proof. exact (eq_refl (@ex (cart _142062 _142063))). Qed.
Lemma lem8009035 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term255 _142062 _142063 _142064 s s' t t') = (term226 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009034 _142062 _142063) (@lem8009033 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009036 {_142062 _142064 : Type'} (x : cart _142062 _142064) (t : type24 _142062 _142064) : (term241 _142062 _142064 x t) = (term241 _142062 _142064 x t).
Proof. exact (eq_refl (term241 _142062 _142064 x t)). Qed.
Lemma lem8009037 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term251 _142062 _142063 _142064 x s s' t t') = (term243 _142062 _142063 _142064 x s s' t t').
Proof. exact (MK_COMB (@lem8009036 _142062 _142064 x t) (@lem8009035 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009038 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8009039 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term256 _142062 _142063 _142064 x s s' t t') = (term257 _142062 _142063 _142064 x s s' t t').
Proof. exact (MK_COMB (@lem8009038) (@lem8009037 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009040 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term253 _142062 _142063 _142064 s s' t t' x) = (term224 _142062 _142063 _142064 s x s' t t').
Proof. exact (eq_refl (term253 _142062 _142063 _142064 s s' t t' x)). Qed.
Lemma lem8009041 {_142062 _142064 : Type'} (x : cart _142062 _142064) (t : type24 _142062 _142064) : (term241 _142062 _142064 x t) = (term241 _142062 _142064 x t).
Proof. exact (eq_refl (term241 _142062 _142064 x t)). Qed.
Lemma lem8009042 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term258 _142062 _142063 _142064 x s s' t t' x') = (term259 _142062 _142063 _142064 x s x' s' t t').
Proof. exact (MK_COMB (@lem8009041 _142062 _142064 x t) (@lem8009040 _142062 _142063 _142064 s x' s' t t')). Qed.
Lemma lem8009043 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term260 _142062 _142063 _142064 x s s' t t') = (term261 _142062 _142063 _142064 x s s' t t').
Proof. exact (fun_ext (fun x' : cart _142062 _142063 => @lem8009042 _142062 _142063 _142064 x s x' s' t t')). Qed.
Lemma lem8009044 {_142062 _142063 : Type'} : (@ex (cart _142062 _142063)) = (@ex (cart _142062 _142063)).
Proof. exact (eq_refl (@ex (cart _142062 _142063))). Qed.
Lemma lem8009045 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term252 _142062 _142063 _142064 x s s' t t') = (term262 _142062 _142063 _142064 x s s' t t').
Proof. exact (MK_COMB (@lem8009044 _142062 _142063) (@lem8009043 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009046 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : ((term251 _142062 _142063 _142064 x s s' t t') = (term252 _142062 _142063 _142064 x s s' t t')) = ((term243 _142062 _142063 _142064 x s s' t t') = (term262 _142062 _142063 _142064 x s s' t t')).
Proof. exact (MK_COMB (@lem8009039 _142062 _142063 _142064 x s s' t t') (@lem8009045 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009047 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term243 _142062 _142063 _142064 x s s' t t') = (term262 _142062 _142063 _142064 x s s' t t').
Proof. exact (EQ_MP (@lem8009046 _142062 _142063 _142064 x s s' t t') (@lem8009031 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009049 {A : Type'} (P : Prop) (Q : A -> Prop) : (term247 A P Q) = (term248 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8009050 {_142062 _142064 : Type'} (P : Prop) (Q : type24 _142062 _142064) : (term249 _142062 _142064 P Q) = (term250 _142062 _142064 P Q).
Proof. exact (@lem8009049 (cart _142062 _142064) P Q). Qed.
Lemma lem8009051 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term263 _142062 _142063 _142064 x s x' s' t t') = (term264 _142062 _142063 _142064 x s x' s' t t').
Proof. exact (@lem8009050 _142062 _142064 (@IN (cart _142062 _142064) x t) (term223 _142062 _142063 _142064 s x' s' t t')). Qed.
Lemma lem8009052 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x' : cart _142062 _142064) (t' : type24 _142062 _142064) : (term265 _142062 _142063 _142064 s x s' t t' x') = (term221 _142062 _142063 _142064 s x s' t x' t').
Proof. exact (eq_refl (term265 _142062 _142063 _142064 s x s' t t' x')). Qed.
Lemma lem8009053 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term266 _142062 _142063 _142064 s x s' t t') = (term223 _142062 _142063 _142064 s x s' t t').
Proof. exact (fun_ext (fun x' : cart _142062 _142064 => @lem8009052 _142062 _142063 _142064 s x s' t x' t')). Qed.
Lemma lem8009054 {_142062 _142064 : Type'} : (@ex (cart _142062 _142064)) = (@ex (cart _142062 _142064)).
Proof. exact (eq_refl (@ex (cart _142062 _142064))). Qed.
Lemma lem8009055 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term267 _142062 _142063 _142064 s x s' t t') = (term224 _142062 _142063 _142064 s x s' t t').
Proof. exact (MK_COMB (@lem8009054 _142062 _142064) (@lem8009053 _142062 _142063 _142064 s x s' t t')). Qed.
Lemma lem8009056 {_142062 _142064 : Type'} (x : cart _142062 _142064) (t : type24 _142062 _142064) : (term241 _142062 _142064 x t) = (term241 _142062 _142064 x t).
Proof. exact (eq_refl (term241 _142062 _142064 x t)). Qed.
Lemma lem8009057 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term263 _142062 _142063 _142064 x s x' s' t t') = (term259 _142062 _142063 _142064 x s x' s' t t').
Proof. exact (MK_COMB (@lem8009056 _142062 _142064 x t) (@lem8009055 _142062 _142063 _142064 s x' s' t t')). Qed.
Lemma lem8009058 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8009059 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term268 _142062 _142063 _142064 x s x' s' t t') = (term269 _142062 _142063 _142064 x s x' s' t t').
Proof. exact (MK_COMB (@lem8009058) (@lem8009057 _142062 _142063 _142064 x s x' s' t t')). Qed.
Lemma lem8009060 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x' : cart _142062 _142064) (t' : type24 _142062 _142064) : (term265 _142062 _142063 _142064 s x s' t t' x') = (term221 _142062 _142063 _142064 s x s' t x' t').
Proof. exact (eq_refl (term265 _142062 _142063 _142064 s x s' t t' x')). Qed.
Lemma lem8009061 {_142062 _142064 : Type'} (x : cart _142062 _142064) (t : type24 _142062 _142064) : (term241 _142062 _142064 x t) = (term241 _142062 _142064 x t).
Proof. exact (eq_refl (term241 _142062 _142064 x t)). Qed.
Lemma lem8009062 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) : (term270 _142062 _142063 _142064 x s x' s' t t' x'') = (term271 _142062 _142063 _142064 x s x' s' t x'' t').
Proof. exact (MK_COMB (@lem8009061 _142062 _142064 x t) (@lem8009060 _142062 _142063 _142064 s x' s' t x'' t')). Qed.
Lemma lem8009063 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term272 _142062 _142063 _142064 x s x' s' t t') = (term273 _142062 _142063 _142064 x s x' s' t t').
Proof. exact (fun_ext (fun x'' : cart _142062 _142064 => @lem8009062 _142062 _142063 _142064 x s x' s' t x'' t')). Qed.
Lemma lem8009064 {_142062 _142064 : Type'} : (@ex (cart _142062 _142064)) = (@ex (cart _142062 _142064)).
Proof. exact (eq_refl (@ex (cart _142062 _142064))). Qed.
Lemma lem8009065 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term264 _142062 _142063 _142064 x s x' s' t t') = (term274 _142062 _142063 _142064 x s x' s' t t').
Proof. exact (MK_COMB (@lem8009064 _142062 _142064) (@lem8009063 _142062 _142063 _142064 x s x' s' t t')). Qed.
Lemma lem8009066 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : ((term263 _142062 _142063 _142064 x s x' s' t t') = (term264 _142062 _142063 _142064 x s x' s' t t')) = ((term259 _142062 _142063 _142064 x s x' s' t t') = (term274 _142062 _142063 _142064 x s x' s' t t')).
Proof. exact (MK_COMB (@lem8009059 _142062 _142063 _142064 x s x' s' t t') (@lem8009065 _142062 _142063 _142064 x s x' s' t t')). Qed.
Lemma lem8009067 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term259 _142062 _142063 _142064 x s x' s' t t') = (term274 _142062 _142063 _142064 x s x' s' t t').
Proof. exact (EQ_MP (@lem8009066 _142062 _142063 _142064 x s x' s' t t') (@lem8009051 _142062 _142063 _142064 x s x' s' t t')). Qed.
Lemma lem8009068 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term261 _142062 _142063 _142064 x s s' t t') = (term275 _142062 _142063 _142064 x s s' t t').
Proof. exact (fun_ext (fun x' : cart _142062 _142063 => @lem8009067 _142062 _142063 _142064 x s x' s' t t')). Qed.
Lemma lem8009069 {_142062 _142063 : Type'} : (@ex (cart _142062 _142063)) = (@ex (cart _142062 _142063)).
Proof. exact (eq_refl (@ex (cart _142062 _142063))). Qed.
Lemma lem8009070 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term262 _142062 _142063 _142064 x s s' t t') = (term276 _142062 _142063 _142064 x s s' t t').
Proof. exact (MK_COMB (@lem8009069 _142062 _142063) (@lem8009068 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009071 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term243 _142062 _142063 _142064 x s s' t t') = (term276 _142062 _142063 _142064 x s s' t t').
Proof. exact (TRANS (@lem8009047 _142062 _142063 _142064 x s s' t t') (@lem8009070 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009072 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term245 _142062 _142063 _142064 s s' t t') = (term277 _142062 _142063 _142064 s s' t t').
Proof. exact (fun_ext (fun x : cart _142062 _142064 => @lem8009071 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009073 {_142062 _142064 : Type'} : (@ex (cart _142062 _142064)) = (@ex (cart _142062 _142064)).
Proof. exact (eq_refl (@ex (cart _142062 _142064))). Qed.
Lemma lem8009074 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term246 _142062 _142063 _142064 s s' t t') = (term278 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009073 _142062 _142064) (@lem8009072 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009075 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term227 _142062 _142063 _142064 s s' t t') = (term278 _142062 _142063 _142064 s s' t t').
Proof. exact (TRANS (@lem8009027 _142062 _142063 _142064 s s' t t') (@lem8009074 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009076 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term174 _142062 _142063 _142064 s s' t t') = (term278 _142062 _142063 _142064 s s' t t').
Proof. exact (TRANS (@lem8009003 _142062 _142063 _142064 s s' t t') (@lem8009075 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009077 {_142062 _142063 : Type'} (s : type24 _142062 _142063) : (term172 _142062 _142063 s) = (term172 _142062 _142063 s).
Proof. exact (eq_refl (term172 _142062 _142063 s)). Qed.
Lemma lem8009078 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term178 _142062 _142063 _142064 s s' t t') = (term279 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009077 _142062 _142063 s) (@lem8009076 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009080 {A : Type'} (P : A -> Prop) (Q : Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem8009081 {_142062 _142063 : Type'} (P : type24 _142062 _142063) (Q : Prop) : (term230 _142062 _142063 P Q) = (term231 _142062 _142063 P Q).
Proof. exact (@lem8009080 (cart _142062 _142063) P Q). Qed.
Lemma lem8009082 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term280 _142062 _142063 _142064 s s' t t') = (term281 _142062 _142063 _142064 s s' t t').
Proof. exact (@lem8009081 _142062 _142063 (term150 _142062 _142063 s) (term278 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009083 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) : (term234 _142062 _142063 s x) = (@IN (cart _142062 _142063) x s).
Proof. exact (eq_refl (term234 _142062 _142063 s x)). Qed.
Lemma lem8009084 {_142062 _142063 : Type'} (s : type24 _142062 _142063) : (term235 _142062 _142063 s) = (term150 _142062 _142063 s).
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8009083 _142062 _142063 x s)). Qed.
Lemma lem8009085 {_142062 _142063 : Type'} : (@ex (cart _142062 _142063)) = (@ex (cart _142062 _142063)).
Proof. exact (eq_refl (@ex (cart _142062 _142063))). Qed.
Lemma lem8009086 {_142062 _142063 : Type'} (s : type24 _142062 _142063) : (term236 _142062 _142063 s) = (term151 _142062 _142063 s).
Proof. exact (MK_COMB (@lem8009085 _142062 _142063) (@lem8009084 _142062 _142063 s)). Qed.
Lemma lem8009087 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8009088 {_142062 _142063 : Type'} (s : type24 _142062 _142063) : (term237 _142062 _142063 s) = (term172 _142062 _142063 s).
Proof. exact (MK_COMB (@lem8009087) (@lem8009086 _142062 _142063 s)). Qed.
Lemma lem8009089 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term278 _142062 _142063 _142064 s s' t t') = (term278 _142062 _142063 _142064 s s' t t').
Proof. exact (eq_refl (term278 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009090 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term280 _142062 _142063 _142064 s s' t t') = (term279 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009088 _142062 _142063 s) (@lem8009089 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009091 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8009092 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term282 _142062 _142063 _142064 s s' t t') = (term283 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009091) (@lem8009090 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009093 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) : (term234 _142062 _142063 s x) = (@IN (cart _142062 _142063) x s).
Proof. exact (eq_refl (term234 _142062 _142063 s x)). Qed.
Lemma lem8009094 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8009095 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) : (term240 _142062 _142063 s x) = (term241 _142062 _142063 x s).
Proof. exact (MK_COMB (@lem8009094) (@lem8009093 _142062 _142063 x s)). Qed.
Lemma lem8009096 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term278 _142062 _142063 _142064 s s' t t') = (term278 _142062 _142063 _142064 s s' t t').
Proof. exact (eq_refl (term278 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009097 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term284 _142062 _142063 _142064 x s s' t t') = (term285 _142062 _142063 _142064 x s s' t t').
Proof. exact (MK_COMB (@lem8009095 _142062 _142063 x s) (@lem8009096 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009098 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term286 _142062 _142063 _142064 s s' t t') = (term287 _142062 _142063 _142064 s s' t t').
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8009097 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009099 {_142062 _142063 : Type'} : (@ex (cart _142062 _142063)) = (@ex (cart _142062 _142063)).
Proof. exact (eq_refl (@ex (cart _142062 _142063))). Qed.
Lemma lem8009100 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term281 _142062 _142063 _142064 s s' t t') = (term288 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009099 _142062 _142063) (@lem8009098 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009101 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : ((term280 _142062 _142063 _142064 s s' t t') = (term281 _142062 _142063 _142064 s s' t t')) = ((term279 _142062 _142063 _142064 s s' t t') = (term288 _142062 _142063 _142064 s s' t t')).
Proof. exact (MK_COMB (@lem8009092 _142062 _142063 _142064 s s' t t') (@lem8009100 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009102 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term279 _142062 _142063 _142064 s s' t t') = (term288 _142062 _142063 _142064 s s' t t').
Proof. exact (EQ_MP (@lem8009101 _142062 _142063 _142064 s s' t t') (@lem8009082 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009104 {A : Type'} (P : Prop) (Q : A -> Prop) : (term247 A P Q) = (term248 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8009105 {_142062 _142064 : Type'} (P : Prop) (Q : type24 _142062 _142064) : (term249 _142062 _142064 P Q) = (term250 _142062 _142064 P Q).
Proof. exact (@lem8009104 (cart _142062 _142064) P Q). Qed.
Lemma lem8009106 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term289 _142062 _142063 _142064 x s s' t t') = (term290 _142062 _142063 _142064 x s s' t t').
Proof. exact (@lem8009105 _142062 _142064 (@IN (cart _142062 _142063) x s) (term277 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009107 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term291 _142062 _142063 _142064 s s' t t' x) = (term276 _142062 _142063 _142064 x s s' t t').
Proof. exact (eq_refl (term291 _142062 _142063 _142064 s s' t t' x)). Qed.
Lemma lem8009108 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term292 _142062 _142063 _142064 s s' t t') = (term277 _142062 _142063 _142064 s s' t t').
Proof. exact (fun_ext (fun x : cart _142062 _142064 => @lem8009107 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009109 {_142062 _142064 : Type'} : (@ex (cart _142062 _142064)) = (@ex (cart _142062 _142064)).
Proof. exact (eq_refl (@ex (cart _142062 _142064))). Qed.
Lemma lem8009110 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term293 _142062 _142063 _142064 s s' t t') = (term278 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009109 _142062 _142064) (@lem8009108 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009111 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) : (term241 _142062 _142063 x s) = (term241 _142062 _142063 x s).
Proof. exact (eq_refl (term241 _142062 _142063 x s)). Qed.
Lemma lem8009112 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term289 _142062 _142063 _142064 x s s' t t') = (term285 _142062 _142063 _142064 x s s' t t').
Proof. exact (MK_COMB (@lem8009111 _142062 _142063 x s) (@lem8009110 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009113 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8009114 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term294 _142062 _142063 _142064 x s s' t t') = (term295 _142062 _142063 _142064 x s s' t t').
Proof. exact (MK_COMB (@lem8009113) (@lem8009112 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009115 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term291 _142062 _142063 _142064 s s' t t' x) = (term276 _142062 _142063 _142064 x s s' t t').
Proof. exact (eq_refl (term291 _142062 _142063 _142064 s s' t t' x)). Qed.
Lemma lem8009116 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) : (term241 _142062 _142063 x s) = (term241 _142062 _142063 x s).
Proof. exact (eq_refl (term241 _142062 _142063 x s)). Qed.
Lemma lem8009117 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term296 _142062 _142063 _142064 x s s' t t' x') = (term297 _142062 _142063 _142064 x x' s s' t t').
Proof. exact (MK_COMB (@lem8009116 _142062 _142063 x s) (@lem8009115 _142062 _142063 _142064 x' s s' t t')). Qed.
Lemma lem8009118 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term298 _142062 _142063 _142064 x s s' t t') = (term299 _142062 _142063 _142064 x s s' t t').
Proof. exact (fun_ext (fun x' : cart _142062 _142064 => @lem8009117 _142062 _142063 _142064 x x' s s' t t')). Qed.
Lemma lem8009119 {_142062 _142064 : Type'} : (@ex (cart _142062 _142064)) = (@ex (cart _142062 _142064)).
Proof. exact (eq_refl (@ex (cart _142062 _142064))). Qed.
Lemma lem8009120 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term290 _142062 _142063 _142064 x s s' t t') = (term300 _142062 _142063 _142064 x s s' t t').
Proof. exact (MK_COMB (@lem8009119 _142062 _142064) (@lem8009118 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009121 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : ((term289 _142062 _142063 _142064 x s s' t t') = (term290 _142062 _142063 _142064 x s s' t t')) = ((term285 _142062 _142063 _142064 x s s' t t') = (term300 _142062 _142063 _142064 x s s' t t')).
Proof. exact (MK_COMB (@lem8009114 _142062 _142063 _142064 x s s' t t') (@lem8009120 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009122 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term285 _142062 _142063 _142064 x s s' t t') = (term300 _142062 _142063 _142064 x s s' t t').
Proof. exact (EQ_MP (@lem8009121 _142062 _142063 _142064 x s s' t t') (@lem8009106 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009124 {A : Type'} (P : Prop) (Q : A -> Prop) : (term247 A P Q) = (term248 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8009125 {_142062 _142063 : Type'} (P : Prop) (Q : type24 _142062 _142063) : (term249 _142062 _142063 P Q) = (term250 _142062 _142063 P Q).
Proof. exact (@lem8009124 (cart _142062 _142063) P Q). Qed.
Lemma lem8009126 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term301 _142062 _142063 _142064 x x' s s' t t') = (term302 _142062 _142063 _142064 x x' s s' t t').
Proof. exact (@lem8009125 _142062 _142063 (@IN (cart _142062 _142063) x s) (term275 _142062 _142063 _142064 x' s s' t t')). Qed.
Lemma lem8009127 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term303 _142062 _142063 _142064 x s s' t t' x') = (term274 _142062 _142063 _142064 x s x' s' t t').
Proof. exact (eq_refl (term303 _142062 _142063 _142064 x s s' t t' x')). Qed.
Lemma lem8009128 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term304 _142062 _142063 _142064 x s s' t t') = (term275 _142062 _142063 _142064 x s s' t t').
Proof. exact (fun_ext (fun x' : cart _142062 _142063 => @lem8009127 _142062 _142063 _142064 x s x' s' t t')). Qed.
Lemma lem8009129 {_142062 _142063 : Type'} : (@ex (cart _142062 _142063)) = (@ex (cart _142062 _142063)).
Proof. exact (eq_refl (@ex (cart _142062 _142063))). Qed.
Lemma lem8009130 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term305 _142062 _142063 _142064 x s s' t t') = (term276 _142062 _142063 _142064 x s s' t t').
Proof. exact (MK_COMB (@lem8009129 _142062 _142063) (@lem8009128 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009131 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) : (term241 _142062 _142063 x s) = (term241 _142062 _142063 x s).
Proof. exact (eq_refl (term241 _142062 _142063 x s)). Qed.
Lemma lem8009132 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term301 _142062 _142063 _142064 x x' s s' t t') = (term297 _142062 _142063 _142064 x x' s s' t t').
Proof. exact (MK_COMB (@lem8009131 _142062 _142063 x s) (@lem8009130 _142062 _142063 _142064 x' s s' t t')). Qed.
Lemma lem8009133 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8009134 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term306 _142062 _142063 _142064 x x' s s' t t') = (term307 _142062 _142063 _142064 x x' s s' t t').
Proof. exact (MK_COMB (@lem8009133) (@lem8009132 _142062 _142063 _142064 x x' s s' t t')). Qed.
Lemma lem8009135 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term303 _142062 _142063 _142064 x s s' t t' x') = (term274 _142062 _142063 _142064 x s x' s' t t').
Proof. exact (eq_refl (term303 _142062 _142063 _142064 x s s' t t' x')). Qed.
Lemma lem8009136 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) : (term241 _142062 _142063 x s) = (term241 _142062 _142063 x s).
Proof. exact (eq_refl (term241 _142062 _142063 x s)). Qed.
Lemma lem8009137 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (x'' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term308 _142062 _142063 _142064 x x' s s' t t' x'') = (term309 _142062 _142063 _142064 x x' s x'' s' t t').
Proof. exact (MK_COMB (@lem8009136 _142062 _142063 x s) (@lem8009135 _142062 _142063 _142064 x' s x'' s' t t')). Qed.
Lemma lem8009138 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term310 _142062 _142063 _142064 x x' s s' t t') = (term311 _142062 _142063 _142064 x x' s s' t t').
Proof. exact (fun_ext (fun x'' : cart _142062 _142063 => @lem8009137 _142062 _142063 _142064 x x' s x'' s' t t')). Qed.
Lemma lem8009139 {_142062 _142063 : Type'} : (@ex (cart _142062 _142063)) = (@ex (cart _142062 _142063)).
Proof. exact (eq_refl (@ex (cart _142062 _142063))). Qed.
Lemma lem8009140 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term302 _142062 _142063 _142064 x x' s s' t t') = (term312 _142062 _142063 _142064 x x' s s' t t').
Proof. exact (MK_COMB (@lem8009139 _142062 _142063) (@lem8009138 _142062 _142063 _142064 x x' s s' t t')). Qed.
Lemma lem8009141 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : ((term301 _142062 _142063 _142064 x x' s s' t t') = (term302 _142062 _142063 _142064 x x' s s' t t')) = ((term297 _142062 _142063 _142064 x x' s s' t t') = (term312 _142062 _142063 _142064 x x' s s' t t')).
Proof. exact (MK_COMB (@lem8009134 _142062 _142063 _142064 x x' s s' t t') (@lem8009140 _142062 _142063 _142064 x x' s s' t t')). Qed.
Lemma lem8009142 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term297 _142062 _142063 _142064 x x' s s' t t') = (term312 _142062 _142063 _142064 x x' s s' t t').
Proof. exact (EQ_MP (@lem8009141 _142062 _142063 _142064 x x' s s' t t') (@lem8009126 _142062 _142063 _142064 x x' s s' t t')). Qed.
Lemma lem8009144 {A : Type'} (P : Prop) (Q : A -> Prop) : (term247 A P Q) = (term248 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8009145 {_142062 _142064 : Type'} (P : Prop) (Q : type24 _142062 _142064) : (term249 _142062 _142064 P Q) = (term250 _142062 _142064 P Q).
Proof. exact (@lem8009144 (cart _142062 _142064) P Q). Qed.
Lemma lem8009146 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (x'' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term313 _142062 _142063 _142064 x x' s x'' s' t t') = (term314 _142062 _142063 _142064 x x' s x'' s' t t').
Proof. exact (@lem8009145 _142062 _142064 (@IN (cart _142062 _142063) x s) (term273 _142062 _142063 _142064 x' s x'' s' t t')). Qed.
Lemma lem8009147 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) : (term315 _142062 _142063 _142064 x s x' s' t t' x'') = (term271 _142062 _142063 _142064 x s x' s' t x'' t').
Proof. exact (eq_refl (term315 _142062 _142063 _142064 x s x' s' t t' x'')). Qed.
Lemma lem8009148 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term316 _142062 _142063 _142064 x s x' s' t t') = (term273 _142062 _142063 _142064 x s x' s' t t').
Proof. exact (fun_ext (fun x'' : cart _142062 _142064 => @lem8009147 _142062 _142063 _142064 x s x' s' t x'' t')). Qed.
Lemma lem8009149 {_142062 _142064 : Type'} : (@ex (cart _142062 _142064)) = (@ex (cart _142062 _142064)).
Proof. exact (eq_refl (@ex (cart _142062 _142064))). Qed.
Lemma lem8009150 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term317 _142062 _142063 _142064 x s x' s' t t') = (term274 _142062 _142063 _142064 x s x' s' t t').
Proof. exact (MK_COMB (@lem8009149 _142062 _142064) (@lem8009148 _142062 _142063 _142064 x s x' s' t t')). Qed.
Lemma lem8009151 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) : (term241 _142062 _142063 x s) = (term241 _142062 _142063 x s).
Proof. exact (eq_refl (term241 _142062 _142063 x s)). Qed.
Lemma lem8009152 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (x'' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term313 _142062 _142063 _142064 x x' s x'' s' t t') = (term309 _142062 _142063 _142064 x x' s x'' s' t t').
Proof. exact (MK_COMB (@lem8009151 _142062 _142063 x s) (@lem8009150 _142062 _142063 _142064 x' s x'' s' t t')). Qed.
Lemma lem8009153 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8009154 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (x'' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term318 _142062 _142063 _142064 x x' s x'' s' t t') = (term319 _142062 _142063 _142064 x x' s x'' s' t t').
Proof. exact (MK_COMB (@lem8009153) (@lem8009152 _142062 _142063 _142064 x x' s x'' s' t t')). Qed.
Lemma lem8009155 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) : (term315 _142062 _142063 _142064 x s x' s' t t' x'') = (term271 _142062 _142063 _142064 x s x' s' t x'' t').
Proof. exact (eq_refl (term315 _142062 _142063 _142064 x s x' s' t t' x'')). Qed.
Lemma lem8009156 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) : (term241 _142062 _142063 x s) = (term241 _142062 _142063 x s).
Proof. exact (eq_refl (term241 _142062 _142063 x s)). Qed.
Lemma lem8009157 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (x'' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x''' : cart _142062 _142064) (t' : type24 _142062 _142064) : (term320 _142062 _142063 _142064 x x' s x'' s' t t' x''') = (term321 _142062 _142063 _142064 x x' s x'' s' t x''' t').
Proof. exact (MK_COMB (@lem8009156 _142062 _142063 x s) (@lem8009155 _142062 _142063 _142064 x' s x'' s' t x''' t')). Qed.
Lemma lem8009158 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (x'' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term322 _142062 _142063 _142064 x x' s x'' s' t t') = (term323 _142062 _142063 _142064 x x' s x'' s' t t').
Proof. exact (fun_ext (fun x''' : cart _142062 _142064 => @lem8009157 _142062 _142063 _142064 x x' s x'' s' t x''' t')). Qed.
Lemma lem8009159 {_142062 _142064 : Type'} : (@ex (cart _142062 _142064)) = (@ex (cart _142062 _142064)).
Proof. exact (eq_refl (@ex (cart _142062 _142064))). Qed.
Lemma lem8009160 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (x'' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term314 _142062 _142063 _142064 x x' s x'' s' t t') = (term324 _142062 _142063 _142064 x x' s x'' s' t t').
Proof. exact (MK_COMB (@lem8009159 _142062 _142064) (@lem8009158 _142062 _142063 _142064 x x' s x'' s' t t')). Qed.
Lemma lem8009161 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (x'' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : ((term313 _142062 _142063 _142064 x x' s x'' s' t t') = (term314 _142062 _142063 _142064 x x' s x'' s' t t')) = ((term309 _142062 _142063 _142064 x x' s x'' s' t t') = (term324 _142062 _142063 _142064 x x' s x'' s' t t')).
Proof. exact (MK_COMB (@lem8009154 _142062 _142063 _142064 x x' s x'' s' t t') (@lem8009160 _142062 _142063 _142064 x x' s x'' s' t t')). Qed.
Lemma lem8009162 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (x'' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term309 _142062 _142063 _142064 x x' s x'' s' t t') = (term324 _142062 _142063 _142064 x x' s x'' s' t t').
Proof. exact (EQ_MP (@lem8009161 _142062 _142063 _142064 x x' s x'' s' t t') (@lem8009146 _142062 _142063 _142064 x x' s x'' s' t t')). Qed.
Lemma lem8009163 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term311 _142062 _142063 _142064 x x' s s' t t') = (term325 _142062 _142063 _142064 x x' s s' t t').
Proof. exact (fun_ext (fun x'' : cart _142062 _142063 => @lem8009162 _142062 _142063 _142064 x x' s x'' s' t t')). Qed.
Lemma lem8009164 {_142062 _142063 : Type'} : (@ex (cart _142062 _142063)) = (@ex (cart _142062 _142063)).
Proof. exact (eq_refl (@ex (cart _142062 _142063))). Qed.
Lemma lem8009165 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term312 _142062 _142063 _142064 x x' s s' t t') = (term326 _142062 _142063 _142064 x x' s s' t t').
Proof. exact (MK_COMB (@lem8009164 _142062 _142063) (@lem8009163 _142062 _142063 _142064 x x' s s' t t')). Qed.
Lemma lem8009166 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term297 _142062 _142063 _142064 x x' s s' t t') = (term326 _142062 _142063 _142064 x x' s s' t t').
Proof. exact (TRANS (@lem8009142 _142062 _142063 _142064 x x' s s' t t') (@lem8009165 _142062 _142063 _142064 x x' s s' t t')). Qed.
Lemma lem8009167 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term299 _142062 _142063 _142064 x s s' t t') = (term327 _142062 _142063 _142064 x s s' t t').
Proof. exact (fun_ext (fun x' : cart _142062 _142064 => @lem8009166 _142062 _142063 _142064 x x' s s' t t')). Qed.
Lemma lem8009168 {_142062 _142064 : Type'} : (@ex (cart _142062 _142064)) = (@ex (cart _142062 _142064)).
Proof. exact (eq_refl (@ex (cart _142062 _142064))). Qed.
Lemma lem8009169 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term300 _142062 _142063 _142064 x s s' t t') = (term328 _142062 _142063 _142064 x s s' t t').
Proof. exact (MK_COMB (@lem8009168 _142062 _142064) (@lem8009167 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009170 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term285 _142062 _142063 _142064 x s s' t t') = (term328 _142062 _142063 _142064 x s s' t t').
Proof. exact (TRANS (@lem8009122 _142062 _142063 _142064 x s s' t t') (@lem8009169 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009171 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term287 _142062 _142063 _142064 s s' t t') = (term329 _142062 _142063 _142064 s s' t t').
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8009170 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009172 {_142062 _142063 : Type'} : (@ex (cart _142062 _142063)) = (@ex (cart _142062 _142063)).
Proof. exact (eq_refl (@ex (cart _142062 _142063))). Qed.
Lemma lem8009173 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term288 _142062 _142063 _142064 s s' t t') = (term330 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009172 _142062 _142063) (@lem8009171 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009174 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term279 _142062 _142063 _142064 s s' t t') = (term330 _142062 _142063 _142064 s s' t t').
Proof. exact (TRANS (@lem8009102 _142062 _142063 _142064 s s' t t') (@lem8009173 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009175 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term178 _142062 _142063 _142064 s s' t t') = (term330 _142062 _142063 _142064 s s' t t').
Proof. exact (TRANS (@lem8009078 _142062 _142063 _142064 s s' t t') (@lem8009174 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009176 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term186 _142062 _142063 _142064 s t s' t') = (term186 _142062 _142063 _142064 s t s' t').
Proof. exact (eq_refl (term186 _142062 _142063 _142064 s t s' t')). Qed.
Lemma lem8009177 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term188 _142062 _142063 _142064 s s' t t') = (term331 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009176 _142062 _142063 _142064 s t s' t') (@lem8009175 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009179 {A : Type'} (P : Prop) (Q : A -> Prop) : (term247 A P Q) = (term248 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8009180 {_142062 _142063 : Type'} (P : Prop) (Q : type24 _142062 _142063) : (term249 _142062 _142063 P Q) = (term250 _142062 _142063 P Q).
Proof. exact (@lem8009179 (cart _142062 _142063) P Q). Qed.
Lemma lem8009181 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term332 _142062 _142063 _142064 s s' t t') = (term333 _142062 _142063 _142064 s s' t t').
Proof. exact (@lem8009180 _142062 _142063 (term143 _142062 _142063 _142064 s t s' t') (term329 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009182 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term334 _142062 _142063 _142064 s s' t t' x) = (term328 _142062 _142063 _142064 x s s' t t').
Proof. exact (eq_refl (term334 _142062 _142063 _142064 s s' t t' x)). Qed.
Lemma lem8009183 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term335 _142062 _142063 _142064 s s' t t') = (term329 _142062 _142063 _142064 s s' t t').
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8009182 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009184 {_142062 _142063 : Type'} : (@ex (cart _142062 _142063)) = (@ex (cart _142062 _142063)).
Proof. exact (eq_refl (@ex (cart _142062 _142063))). Qed.
Lemma lem8009185 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term336 _142062 _142063 _142064 s s' t t') = (term330 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009184 _142062 _142063) (@lem8009183 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009186 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term186 _142062 _142063 _142064 s t s' t') = (term186 _142062 _142063 _142064 s t s' t').
Proof. exact (eq_refl (term186 _142062 _142063 _142064 s t s' t')). Qed.
Lemma lem8009187 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term332 _142062 _142063 _142064 s s' t t') = (term331 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009186 _142062 _142063 _142064 s t s' t') (@lem8009185 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009188 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8009189 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term337 _142062 _142063 _142064 s s' t t') = (term338 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009188) (@lem8009187 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009190 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term334 _142062 _142063 _142064 s s' t t' x) = (term328 _142062 _142063 _142064 x s s' t t').
Proof. exact (eq_refl (term334 _142062 _142063 _142064 s s' t t' x)). Qed.
Lemma lem8009191 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term186 _142062 _142063 _142064 s t s' t') = (term186 _142062 _142063 _142064 s t s' t').
Proof. exact (eq_refl (term186 _142062 _142063 _142064 s t s' t')). Qed.
Lemma lem8009192 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term339 _142062 _142063 _142064 s s' t t' x) = (term340 _142062 _142063 _142064 x s s' t t').
Proof. exact (MK_COMB (@lem8009191 _142062 _142063 _142064 s t s' t') (@lem8009190 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009193 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term341 _142062 _142063 _142064 s s' t t') = (term342 _142062 _142063 _142064 s s' t t').
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8009192 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009194 {_142062 _142063 : Type'} : (@ex (cart _142062 _142063)) = (@ex (cart _142062 _142063)).
Proof. exact (eq_refl (@ex (cart _142062 _142063))). Qed.
Lemma lem8009195 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term333 _142062 _142063 _142064 s s' t t') = (term343 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009194 _142062 _142063) (@lem8009193 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009196 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : ((term332 _142062 _142063 _142064 s s' t t') = (term333 _142062 _142063 _142064 s s' t t')) = ((term331 _142062 _142063 _142064 s s' t t') = (term343 _142062 _142063 _142064 s s' t t')).
Proof. exact (MK_COMB (@lem8009189 _142062 _142063 _142064 s s' t t') (@lem8009195 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009197 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term331 _142062 _142063 _142064 s s' t t') = (term343 _142062 _142063 _142064 s s' t t').
Proof. exact (EQ_MP (@lem8009196 _142062 _142063 _142064 s s' t t') (@lem8009181 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009199 {A : Type'} (P : Prop) (Q : A -> Prop) : (term247 A P Q) = (term248 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8009200 {_142062 _142064 : Type'} (P : Prop) (Q : type24 _142062 _142064) : (term249 _142062 _142064 P Q) = (term250 _142062 _142064 P Q).
Proof. exact (@lem8009199 (cart _142062 _142064) P Q). Qed.
Lemma lem8009201 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term344 _142062 _142063 _142064 x s s' t t') = (term345 _142062 _142063 _142064 x s s' t t').
Proof. exact (@lem8009200 _142062 _142064 (term143 _142062 _142063 _142064 s t s' t') (term327 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009202 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term346 _142062 _142063 _142064 x s s' t t' x') = (term326 _142062 _142063 _142064 x x' s s' t t').
Proof. exact (eq_refl (term346 _142062 _142063 _142064 x s s' t t' x')). Qed.
Lemma lem8009203 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term347 _142062 _142063 _142064 x s s' t t') = (term327 _142062 _142063 _142064 x s s' t t').
Proof. exact (fun_ext (fun x' : cart _142062 _142064 => @lem8009202 _142062 _142063 _142064 x x' s s' t t')). Qed.
Lemma lem8009204 {_142062 _142064 : Type'} : (@ex (cart _142062 _142064)) = (@ex (cart _142062 _142064)).
Proof. exact (eq_refl (@ex (cart _142062 _142064))). Qed.
Lemma lem8009205 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term348 _142062 _142063 _142064 x s s' t t') = (term328 _142062 _142063 _142064 x s s' t t').
Proof. exact (MK_COMB (@lem8009204 _142062 _142064) (@lem8009203 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009206 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term186 _142062 _142063 _142064 s t s' t') = (term186 _142062 _142063 _142064 s t s' t').
Proof. exact (eq_refl (term186 _142062 _142063 _142064 s t s' t')). Qed.
Lemma lem8009207 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term344 _142062 _142063 _142064 x s s' t t') = (term340 _142062 _142063 _142064 x s s' t t').
Proof. exact (MK_COMB (@lem8009206 _142062 _142063 _142064 s t s' t') (@lem8009205 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009208 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8009209 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term349 _142062 _142063 _142064 x s s' t t') = (term350 _142062 _142063 _142064 x s s' t t').
Proof. exact (MK_COMB (@lem8009208) (@lem8009207 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009210 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term346 _142062 _142063 _142064 x s s' t t' x') = (term326 _142062 _142063 _142064 x x' s s' t t').
Proof. exact (eq_refl (term346 _142062 _142063 _142064 x s s' t t' x')). Qed.
Lemma lem8009211 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term186 _142062 _142063 _142064 s t s' t') = (term186 _142062 _142063 _142064 s t s' t').
Proof. exact (eq_refl (term186 _142062 _142063 _142064 s t s' t')). Qed.
Lemma lem8009212 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term351 _142062 _142063 _142064 x s s' t t' x') = (term352 _142062 _142063 _142064 x x' s s' t t').
Proof. exact (MK_COMB (@lem8009211 _142062 _142063 _142064 s t s' t') (@lem8009210 _142062 _142063 _142064 x x' s s' t t')). Qed.
Lemma lem8009213 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term353 _142062 _142063 _142064 x s s' t t') = (term354 _142062 _142063 _142064 x s s' t t').
Proof. exact (fun_ext (fun x' : cart _142062 _142064 => @lem8009212 _142062 _142063 _142064 x x' s s' t t')). Qed.
Lemma lem8009214 {_142062 _142064 : Type'} : (@ex (cart _142062 _142064)) = (@ex (cart _142062 _142064)).
Proof. exact (eq_refl (@ex (cart _142062 _142064))). Qed.
Lemma lem8009215 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term345 _142062 _142063 _142064 x s s' t t') = (term355 _142062 _142063 _142064 x s s' t t').
Proof. exact (MK_COMB (@lem8009214 _142062 _142064) (@lem8009213 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009216 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : ((term344 _142062 _142063 _142064 x s s' t t') = (term345 _142062 _142063 _142064 x s s' t t')) = ((term340 _142062 _142063 _142064 x s s' t t') = (term355 _142062 _142063 _142064 x s s' t t')).
Proof. exact (MK_COMB (@lem8009209 _142062 _142063 _142064 x s s' t t') (@lem8009215 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009217 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term340 _142062 _142063 _142064 x s s' t t') = (term355 _142062 _142063 _142064 x s s' t t').
Proof. exact (EQ_MP (@lem8009216 _142062 _142063 _142064 x s s' t t') (@lem8009201 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009219 {A : Type'} (P : Prop) (Q : A -> Prop) : (term247 A P Q) = (term248 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8009220 {_142062 _142063 : Type'} (P : Prop) (Q : type24 _142062 _142063) : (term249 _142062 _142063 P Q) = (term250 _142062 _142063 P Q).
Proof. exact (@lem8009219 (cart _142062 _142063) P Q). Qed.
Lemma lem8009221 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term356 _142062 _142063 _142064 x x' s s' t t') = (term357 _142062 _142063 _142064 x x' s s' t t').
Proof. exact (@lem8009220 _142062 _142063 (term143 _142062 _142063 _142064 s t s' t') (term325 _142062 _142063 _142064 x x' s s' t t')). Qed.
Lemma lem8009222 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (x'' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term358 _142062 _142063 _142064 x x' s s' t t' x'') = (term324 _142062 _142063 _142064 x x' s x'' s' t t').
Proof. exact (eq_refl (term358 _142062 _142063 _142064 x x' s s' t t' x'')). Qed.
Lemma lem8009223 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term359 _142062 _142063 _142064 x x' s s' t t') = (term325 _142062 _142063 _142064 x x' s s' t t').
Proof. exact (fun_ext (fun x'' : cart _142062 _142063 => @lem8009222 _142062 _142063 _142064 x x' s x'' s' t t')). Qed.
Lemma lem8009224 {_142062 _142063 : Type'} : (@ex (cart _142062 _142063)) = (@ex (cart _142062 _142063)).
Proof. exact (eq_refl (@ex (cart _142062 _142063))). Qed.
Lemma lem8009225 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term360 _142062 _142063 _142064 x x' s s' t t') = (term326 _142062 _142063 _142064 x x' s s' t t').
Proof. exact (MK_COMB (@lem8009224 _142062 _142063) (@lem8009223 _142062 _142063 _142064 x x' s s' t t')). Qed.
Lemma lem8009226 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term186 _142062 _142063 _142064 s t s' t') = (term186 _142062 _142063 _142064 s t s' t').
Proof. exact (eq_refl (term186 _142062 _142063 _142064 s t s' t')). Qed.
Lemma lem8009227 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term356 _142062 _142063 _142064 x x' s s' t t') = (term352 _142062 _142063 _142064 x x' s s' t t').
Proof. exact (MK_COMB (@lem8009226 _142062 _142063 _142064 s t s' t') (@lem8009225 _142062 _142063 _142064 x x' s s' t t')). Qed.
Lemma lem8009228 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8009229 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term361 _142062 _142063 _142064 x x' s s' t t') = (term362 _142062 _142063 _142064 x x' s s' t t').
Proof. exact (MK_COMB (@lem8009228) (@lem8009227 _142062 _142063 _142064 x x' s s' t t')). Qed.
Lemma lem8009230 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (x'' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term358 _142062 _142063 _142064 x x' s s' t t' x'') = (term324 _142062 _142063 _142064 x x' s x'' s' t t').
Proof. exact (eq_refl (term358 _142062 _142063 _142064 x x' s s' t t' x'')). Qed.
Lemma lem8009231 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term186 _142062 _142063 _142064 s t s' t') = (term186 _142062 _142063 _142064 s t s' t').
Proof. exact (eq_refl (term186 _142062 _142063 _142064 s t s' t')). Qed.
Lemma lem8009232 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (x'' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term363 _142062 _142063 _142064 x x' s s' t t' x'') = (term364 _142062 _142063 _142064 x x' s x'' s' t t').
Proof. exact (MK_COMB (@lem8009231 _142062 _142063 _142064 s t s' t') (@lem8009230 _142062 _142063 _142064 x x' s x'' s' t t')). Qed.
Lemma lem8009233 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term365 _142062 _142063 _142064 x x' s s' t t') = (term366 _142062 _142063 _142064 x x' s s' t t').
Proof. exact (fun_ext (fun x'' : cart _142062 _142063 => @lem8009232 _142062 _142063 _142064 x x' s x'' s' t t')). Qed.
Lemma lem8009234 {_142062 _142063 : Type'} : (@ex (cart _142062 _142063)) = (@ex (cart _142062 _142063)).
Proof. exact (eq_refl (@ex (cart _142062 _142063))). Qed.
Lemma lem8009235 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term357 _142062 _142063 _142064 x x' s s' t t') = (term367 _142062 _142063 _142064 x x' s s' t t').
Proof. exact (MK_COMB (@lem8009234 _142062 _142063) (@lem8009233 _142062 _142063 _142064 x x' s s' t t')). Qed.
Lemma lem8009236 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : ((term356 _142062 _142063 _142064 x x' s s' t t') = (term357 _142062 _142063 _142064 x x' s s' t t')) = ((term352 _142062 _142063 _142064 x x' s s' t t') = (term367 _142062 _142063 _142064 x x' s s' t t')).
Proof. exact (MK_COMB (@lem8009229 _142062 _142063 _142064 x x' s s' t t') (@lem8009235 _142062 _142063 _142064 x x' s s' t t')). Qed.
Lemma lem8009237 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term352 _142062 _142063 _142064 x x' s s' t t') = (term367 _142062 _142063 _142064 x x' s s' t t').
Proof. exact (EQ_MP (@lem8009236 _142062 _142063 _142064 x x' s s' t t') (@lem8009221 _142062 _142063 _142064 x x' s s' t t')). Qed.
Lemma lem8009239 {A : Type'} (P : Prop) (Q : A -> Prop) : (term247 A P Q) = (term248 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8009240 {_142062 _142064 : Type'} (P : Prop) (Q : type24 _142062 _142064) : (term249 _142062 _142064 P Q) = (term250 _142062 _142064 P Q).
Proof. exact (@lem8009239 (cart _142062 _142064) P Q). Qed.
Lemma lem8009241 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (x'' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term368 _142062 _142063 _142064 x x' s x'' s' t t') = (term369 _142062 _142063 _142064 x x' s x'' s' t t').
Proof. exact (@lem8009240 _142062 _142064 (term143 _142062 _142063 _142064 s t s' t') (term323 _142062 _142063 _142064 x x' s x'' s' t t')). Qed.
Lemma lem8009242 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (x'' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x''' : cart _142062 _142064) (t' : type24 _142062 _142064) : (term370 _142062 _142063 _142064 x x' s x'' s' t t' x''') = (term321 _142062 _142063 _142064 x x' s x'' s' t x''' t').
Proof. exact (eq_refl (term370 _142062 _142063 _142064 x x' s x'' s' t t' x''')). Qed.
Lemma lem8009243 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (x'' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term371 _142062 _142063 _142064 x x' s x'' s' t t') = (term323 _142062 _142063 _142064 x x' s x'' s' t t').
Proof. exact (fun_ext (fun x''' : cart _142062 _142064 => @lem8009242 _142062 _142063 _142064 x x' s x'' s' t x''' t')). Qed.
Lemma lem8009244 {_142062 _142064 : Type'} : (@ex (cart _142062 _142064)) = (@ex (cart _142062 _142064)).
Proof. exact (eq_refl (@ex (cart _142062 _142064))). Qed.
Lemma lem8009245 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (x'' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term372 _142062 _142063 _142064 x x' s x'' s' t t') = (term324 _142062 _142063 _142064 x x' s x'' s' t t').
Proof. exact (MK_COMB (@lem8009244 _142062 _142064) (@lem8009243 _142062 _142063 _142064 x x' s x'' s' t t')). Qed.
Lemma lem8009246 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term186 _142062 _142063 _142064 s t s' t') = (term186 _142062 _142063 _142064 s t s' t').
Proof. exact (eq_refl (term186 _142062 _142063 _142064 s t s' t')). Qed.
Lemma lem8009247 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (x'' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term368 _142062 _142063 _142064 x x' s x'' s' t t') = (term364 _142062 _142063 _142064 x x' s x'' s' t t').
Proof. exact (MK_COMB (@lem8009246 _142062 _142063 _142064 s t s' t') (@lem8009245 _142062 _142063 _142064 x x' s x'' s' t t')). Qed.
Lemma lem8009248 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8009249 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (x'' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term373 _142062 _142063 _142064 x x' s x'' s' t t') = (term374 _142062 _142063 _142064 x x' s x'' s' t t').
Proof. exact (MK_COMB (@lem8009248) (@lem8009247 _142062 _142063 _142064 x x' s x'' s' t t')). Qed.
Lemma lem8009250 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (x'' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x''' : cart _142062 _142064) (t' : type24 _142062 _142064) : (term370 _142062 _142063 _142064 x x' s x'' s' t t' x''') = (term321 _142062 _142063 _142064 x x' s x'' s' t x''' t').
Proof. exact (eq_refl (term370 _142062 _142063 _142064 x x' s x'' s' t t' x''')). Qed.
Lemma lem8009251 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term186 _142062 _142063 _142064 s t s' t') = (term186 _142062 _142063 _142064 s t s' t').
Proof. exact (eq_refl (term186 _142062 _142063 _142064 s t s' t')). Qed.
Lemma lem8009252 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (x'' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x''' : cart _142062 _142064) (t' : type24 _142062 _142064) : (term375 _142062 _142063 _142064 x x' s x'' s' t t' x''') = (term376 _142062 _142063 _142064 x x' s x'' s' t x''' t').
Proof. exact (MK_COMB (@lem8009251 _142062 _142063 _142064 s t s' t') (@lem8009250 _142062 _142063 _142064 x x' s x'' s' t x''' t')). Qed.
Lemma lem8009253 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (x'' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term377 _142062 _142063 _142064 x x' s x'' s' t t') = (term378 _142062 _142063 _142064 x x' s x'' s' t t').
Proof. exact (fun_ext (fun x''' : cart _142062 _142064 => @lem8009252 _142062 _142063 _142064 x x' s x'' s' t x''' t')). Qed.
Lemma lem8009254 {_142062 _142064 : Type'} : (@ex (cart _142062 _142064)) = (@ex (cart _142062 _142064)).
Proof. exact (eq_refl (@ex (cart _142062 _142064))). Qed.
Lemma lem8009255 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (x'' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term369 _142062 _142063 _142064 x x' s x'' s' t t') = (term379 _142062 _142063 _142064 x x' s x'' s' t t').
Proof. exact (MK_COMB (@lem8009254 _142062 _142064) (@lem8009253 _142062 _142063 _142064 x x' s x'' s' t t')). Qed.
Lemma lem8009256 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (x'' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : ((term368 _142062 _142063 _142064 x x' s x'' s' t t') = (term369 _142062 _142063 _142064 x x' s x'' s' t t')) = ((term364 _142062 _142063 _142064 x x' s x'' s' t t') = (term379 _142062 _142063 _142064 x x' s x'' s' t t')).
Proof. exact (MK_COMB (@lem8009249 _142062 _142063 _142064 x x' s x'' s' t t') (@lem8009255 _142062 _142063 _142064 x x' s x'' s' t t')). Qed.
Lemma lem8009257 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (x'' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term364 _142062 _142063 _142064 x x' s x'' s' t t') = (term379 _142062 _142063 _142064 x x' s x'' s' t t').
Proof. exact (EQ_MP (@lem8009256 _142062 _142063 _142064 x x' s x'' s' t t') (@lem8009241 _142062 _142063 _142064 x x' s x'' s' t t')). Qed.
Lemma lem8009258 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term366 _142062 _142063 _142064 x x' s s' t t') = (term380 _142062 _142063 _142064 x x' s s' t t').
Proof. exact (fun_ext (fun x'' : cart _142062 _142063 => @lem8009257 _142062 _142063 _142064 x x' s x'' s' t t')). Qed.
Lemma lem8009259 {_142062 _142063 : Type'} : (@ex (cart _142062 _142063)) = (@ex (cart _142062 _142063)).
Proof. exact (eq_refl (@ex (cart _142062 _142063))). Qed.
Lemma lem8009260 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term367 _142062 _142063 _142064 x x' s s' t t') = (term381 _142062 _142063 _142064 x x' s s' t t').
Proof. exact (MK_COMB (@lem8009259 _142062 _142063) (@lem8009258 _142062 _142063 _142064 x x' s s' t t')). Qed.
Lemma lem8009261 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (x' : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term352 _142062 _142063 _142064 x x' s s' t t') = (term381 _142062 _142063 _142064 x x' s s' t t').
Proof. exact (TRANS (@lem8009237 _142062 _142063 _142064 x x' s s' t t') (@lem8009260 _142062 _142063 _142064 x x' s s' t t')). Qed.
Lemma lem8009262 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term354 _142062 _142063 _142064 x s s' t t') = (term382 _142062 _142063 _142064 x s s' t t').
Proof. exact (fun_ext (fun x' : cart _142062 _142064 => @lem8009261 _142062 _142063 _142064 x x' s s' t t')). Qed.
Lemma lem8009263 {_142062 _142064 : Type'} : (@ex (cart _142062 _142064)) = (@ex (cart _142062 _142064)).
Proof. exact (eq_refl (@ex (cart _142062 _142064))). Qed.
Lemma lem8009264 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term355 _142062 _142063 _142064 x s s' t t') = (term383 _142062 _142063 _142064 x s s' t t').
Proof. exact (MK_COMB (@lem8009263 _142062 _142064) (@lem8009262 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009265 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term340 _142062 _142063 _142064 x s s' t t') = (term383 _142062 _142063 _142064 x s s' t t').
Proof. exact (TRANS (@lem8009217 _142062 _142063 _142064 x s s' t t') (@lem8009264 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009266 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term342 _142062 _142063 _142064 s s' t t') = (term384 _142062 _142063 _142064 s s' t t').
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8009265 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009267 {_142062 _142063 : Type'} : (@ex (cart _142062 _142063)) = (@ex (cart _142062 _142063)).
Proof. exact (eq_refl (@ex (cart _142062 _142063))). Qed.
Lemma lem8009268 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term343 _142062 _142063 _142064 s s' t t') = (term385 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009267 _142062 _142063) (@lem8009266 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009269 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term331 _142062 _142063 _142064 s s' t t') = (term385 _142062 _142063 _142064 s s' t t').
Proof. exact (TRANS (@lem8009197 _142062 _142063 _142064 s s' t t') (@lem8009268 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009270 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term188 _142062 _142063 _142064 s s' t t') = (term385 _142062 _142063 _142064 s s' t t').
Proof. exact (TRANS (@lem8009177 _142062 _142063 _142064 s s' t t') (@lem8009269 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009271 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8009272 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term190 _142062 _142063 _142064 s s' t t') = (term386 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009271) (@lem8009270 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009274 {A : Type'} (P : A -> Prop) (Q : Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem8009275 {_142062 _142063 : Type'} (P : type24 _142062 _142063) (Q : Prop) : (term230 _142062 _142063 P Q) = (term231 _142062 _142063 P Q).
Proof. exact (@lem8009274 (cart _142062 _142063) P Q). Qed.
Lemma lem8009276 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term387 _142062 _142063 _142064 s s' t t') = (term388 _142062 _142063 _142064 s s' t t').
Proof. exact (@lem8009275 _142062 _142063 (term140 _142062 _142063 _142064 s t s' t') (term180 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009277 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term389 _142062 _142063 _142064 s t s' t' x) = (term132 _142062 _142063 _142064 s t x s' t').
Proof. exact (eq_refl (term389 _142062 _142063 _142064 s t s' t' x)). Qed.
Lemma lem8009278 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term390 _142062 _142063 _142064 s t s' t') = (term140 _142062 _142063 _142064 s t s' t').
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8009277 _142062 _142063 _142064 s t x s' t')). Qed.
Lemma lem8009279 {_142062 _142063 : Type'} : (@ex (cart _142062 _142063)) = (@ex (cart _142062 _142063)).
Proof. exact (eq_refl (@ex (cart _142062 _142063))). Qed.
Lemma lem8009280 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term391 _142062 _142063 _142064 s t s' t') = (term141 _142062 _142063 _142064 s t s' t').
Proof. exact (MK_COMB (@lem8009279 _142062 _142063) (@lem8009278 _142062 _142063 _142064 s t s' t')). Qed.
Lemma lem8009281 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8009282 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term392 _142062 _142063 _142064 s t s' t') = (term182 _142062 _142063 _142064 s t s' t').
Proof. exact (MK_COMB (@lem8009281) (@lem8009280 _142062 _142063 _142064 s t s' t')). Qed.
Lemma lem8009283 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term180 _142062 _142063 _142064 s s' t t') = (term180 _142062 _142063 _142064 s s' t t').
Proof. exact (eq_refl (term180 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009284 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term387 _142062 _142063 _142064 s s' t t') = (term184 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009282 _142062 _142063 _142064 s t s' t') (@lem8009283 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009285 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8009286 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term393 _142062 _142063 _142064 s s' t t') = (term394 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009285) (@lem8009284 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009287 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term389 _142062 _142063 _142064 s t s' t' x) = (term132 _142062 _142063 _142064 s t x s' t').
Proof. exact (eq_refl (term389 _142062 _142063 _142064 s t s' t' x)). Qed.
Lemma lem8009288 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8009289 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term395 _142062 _142063 _142064 s t s' t' x) = (term396 _142062 _142063 _142064 s t x s' t').
Proof. exact (MK_COMB (@lem8009288) (@lem8009287 _142062 _142063 _142064 s t x s' t')). Qed.
Lemma lem8009290 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term180 _142062 _142063 _142064 s s' t t') = (term180 _142062 _142063 _142064 s s' t t').
Proof. exact (eq_refl (term180 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009291 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term397 _142062 _142063 _142064 x s s' t t') = (term398 _142062 _142063 _142064 x s s' t t').
Proof. exact (MK_COMB (@lem8009289 _142062 _142063 _142064 s t x s' t') (@lem8009290 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009292 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term399 _142062 _142063 _142064 s s' t t') = (term400 _142062 _142063 _142064 s s' t t').
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8009291 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009293 {_142062 _142063 : Type'} : (@ex (cart _142062 _142063)) = (@ex (cart _142062 _142063)).
Proof. exact (eq_refl (@ex (cart _142062 _142063))). Qed.
Lemma lem8009294 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term388 _142062 _142063 _142064 s s' t t') = (term401 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009293 _142062 _142063) (@lem8009292 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009295 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : ((term387 _142062 _142063 _142064 s s' t t') = (term388 _142062 _142063 _142064 s s' t t')) = ((term184 _142062 _142063 _142064 s s' t t') = (term401 _142062 _142063 _142064 s s' t t')).
Proof. exact (MK_COMB (@lem8009286 _142062 _142063 _142064 s s' t t') (@lem8009294 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009296 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term184 _142062 _142063 _142064 s s' t t') = (term401 _142062 _142063 _142064 s s' t t').
Proof. exact (EQ_MP (@lem8009295 _142062 _142063 _142064 s s' t t') (@lem8009276 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009298 {A : Type'} (P : A -> Prop) (Q : Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem8009299 {_142062 _142064 : Type'} (P : type24 _142062 _142064) (Q : Prop) : (term230 _142062 _142064 P Q) = (term231 _142062 _142064 P Q).
Proof. exact (@lem8009298 (cart _142062 _142064) P Q). Qed.
Lemma lem8009300 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term402 _142062 _142063 _142064 x s s' t t') = (term403 _142062 _142063 _142064 x s s' t t').
Proof. exact (@lem8009299 _142062 _142064 (term131 _142062 _142063 _142064 s t x s' t') (term180 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009301 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (y : cart _142062 _142064) (t' : type24 _142062 _142064) : (term404 _142062 _142063 _142064 s t x s' t' y) = (term118 _142062 _142063 _142064 s t x s' y t').
Proof. exact (eq_refl (term404 _142062 _142063 _142064 s t x s' t' y)). Qed.
Lemma lem8009302 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term405 _142062 _142063 _142064 s t x s' t') = (term131 _142062 _142063 _142064 s t x s' t').
Proof. exact (fun_ext (fun y : cart _142062 _142064 => @lem8009301 _142062 _142063 _142064 s t x s' y t')). Qed.
Lemma lem8009303 {_142062 _142064 : Type'} : (@ex (cart _142062 _142064)) = (@ex (cart _142062 _142064)).
Proof. exact (eq_refl (@ex (cart _142062 _142064))). Qed.
Lemma lem8009304 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term406 _142062 _142063 _142064 s t x s' t') = (term132 _142062 _142063 _142064 s t x s' t').
Proof. exact (MK_COMB (@lem8009303 _142062 _142064) (@lem8009302 _142062 _142063 _142064 s t x s' t')). Qed.
Lemma lem8009305 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8009306 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term407 _142062 _142063 _142064 s t x s' t') = (term396 _142062 _142063 _142064 s t x s' t').
Proof. exact (MK_COMB (@lem8009305) (@lem8009304 _142062 _142063 _142064 s t x s' t')). Qed.
Lemma lem8009307 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term180 _142062 _142063 _142064 s s' t t') = (term180 _142062 _142063 _142064 s s' t t').
Proof. exact (eq_refl (term180 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009308 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term402 _142062 _142063 _142064 x s s' t t') = (term398 _142062 _142063 _142064 x s s' t t').
Proof. exact (MK_COMB (@lem8009306 _142062 _142063 _142064 s t x s' t') (@lem8009307 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009309 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8009310 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term408 _142062 _142063 _142064 x s s' t t') = (term409 _142062 _142063 _142064 x s s' t t').
Proof. exact (MK_COMB (@lem8009309) (@lem8009308 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009311 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (y : cart _142062 _142064) (t' : type24 _142062 _142064) : (term404 _142062 _142063 _142064 s t x s' t' y) = (term118 _142062 _142063 _142064 s t x s' y t').
Proof. exact (eq_refl (term404 _142062 _142063 _142064 s t x s' t' y)). Qed.
Lemma lem8009312 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8009313 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (y : cart _142062 _142064) (t' : type24 _142062 _142064) : (term410 _142062 _142063 _142064 s t x s' t' y) = (term411 _142062 _142063 _142064 s t x s' y t').
Proof. exact (MK_COMB (@lem8009312) (@lem8009311 _142062 _142063 _142064 s t x s' y t')). Qed.
Lemma lem8009314 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term180 _142062 _142063 _142064 s s' t t') = (term180 _142062 _142063 _142064 s s' t t').
Proof. exact (eq_refl (term180 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009315 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term412 _142062 _142063 _142064 x y s s' t t') = (term413 _142062 _142063 _142064 x y s s' t t').
Proof. exact (MK_COMB (@lem8009313 _142062 _142063 _142064 s t x s' y t') (@lem8009314 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009316 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term414 _142062 _142063 _142064 x s s' t t') = (term415 _142062 _142063 _142064 x s s' t t').
Proof. exact (fun_ext (fun y : cart _142062 _142064 => @lem8009315 _142062 _142063 _142064 x y s s' t t')). Qed.
Lemma lem8009317 {_142062 _142064 : Type'} : (@ex (cart _142062 _142064)) = (@ex (cart _142062 _142064)).
Proof. exact (eq_refl (@ex (cart _142062 _142064))). Qed.
Lemma lem8009318 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term403 _142062 _142063 _142064 x s s' t t') = (term416 _142062 _142063 _142064 x s s' t t').
Proof. exact (MK_COMB (@lem8009317 _142062 _142064) (@lem8009316 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009319 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : ((term402 _142062 _142063 _142064 x s s' t t') = (term403 _142062 _142063 _142064 x s s' t t')) = ((term398 _142062 _142063 _142064 x s s' t t') = (term416 _142062 _142063 _142064 x s s' t t')).
Proof. exact (MK_COMB (@lem8009310 _142062 _142063 _142064 x s s' t t') (@lem8009318 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009320 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term398 _142062 _142063 _142064 x s s' t t') = (term416 _142062 _142063 _142064 x s s' t t').
Proof. exact (EQ_MP (@lem8009319 _142062 _142063 _142064 x s s' t t') (@lem8009300 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009321 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term400 _142062 _142063 _142064 s s' t t') = (term417 _142062 _142063 _142064 s s' t t').
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8009320 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009322 {_142062 _142063 : Type'} : (@ex (cart _142062 _142063)) = (@ex (cart _142062 _142063)).
Proof. exact (eq_refl (@ex (cart _142062 _142063))). Qed.
Lemma lem8009323 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term401 _142062 _142063 _142064 s s' t t') = (term418 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009322 _142062 _142063) (@lem8009321 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009324 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term184 _142062 _142063 _142064 s s' t t') = (term418 _142062 _142063 _142064 s s' t t').
Proof. exact (TRANS (@lem8009296 _142062 _142063 _142064 s s' t t') (@lem8009323 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009325 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term192 _142062 _142063 _142064 s s' t t') = (term419 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009272 _142062 _142063 _142064 s s' t t') (@lem8009324 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009327 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term420 A P Q) = (term421 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem8009328 {_142062 _142063 : Type'} (P : type24 _142062 _142063) (Q : type24 _142062 _142063) : (term422 _142062 _142063 P Q) = (term423 _142062 _142063 P Q).
Proof. exact (@lem8009327 (cart _142062 _142063) P Q). Qed.
Lemma lem8009329 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term424 _142062 _142063 _142064 s s' t t') = (term425 _142062 _142063 _142064 s s' t t').
Proof. exact (@lem8009328 _142062 _142063 (term384 _142062 _142063 _142064 s s' t t') (term417 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009330 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term426 _142062 _142063 _142064 s s' t t' x) = (term383 _142062 _142063 _142064 x s s' t t').
Proof. exact (eq_refl (term426 _142062 _142063 _142064 s s' t t' x)). Qed.
Lemma lem8009331 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term427 _142062 _142063 _142064 s s' t t') = (term384 _142062 _142063 _142064 s s' t t').
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8009330 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009332 {_142062 _142063 : Type'} : (@ex (cart _142062 _142063)) = (@ex (cart _142062 _142063)).
Proof. exact (eq_refl (@ex (cart _142062 _142063))). Qed.
Lemma lem8009333 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term428 _142062 _142063 _142064 s s' t t') = (term385 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009332 _142062 _142063) (@lem8009331 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009334 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8009335 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term429 _142062 _142063 _142064 s s' t t') = (term386 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009334) (@lem8009333 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009336 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term430 _142062 _142063 _142064 s s' t t' x) = (term416 _142062 _142063 _142064 x s s' t t').
Proof. exact (eq_refl (term430 _142062 _142063 _142064 s s' t t' x)). Qed.
Lemma lem8009337 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term431 _142062 _142063 _142064 s s' t t') = (term417 _142062 _142063 _142064 s s' t t').
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8009336 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009338 {_142062 _142063 : Type'} : (@ex (cart _142062 _142063)) = (@ex (cart _142062 _142063)).
Proof. exact (eq_refl (@ex (cart _142062 _142063))). Qed.
Lemma lem8009339 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term432 _142062 _142063 _142064 s s' t t') = (term418 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009338 _142062 _142063) (@lem8009337 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009340 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term424 _142062 _142063 _142064 s s' t t') = (term419 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009335 _142062 _142063 _142064 s s' t t') (@lem8009339 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009341 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8009342 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term433 _142062 _142063 _142064 s s' t t') = (term434 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009341) (@lem8009340 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009343 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term426 _142062 _142063 _142064 s s' t t' x) = (term383 _142062 _142063 _142064 x s s' t t').
Proof. exact (eq_refl (term426 _142062 _142063 _142064 s s' t t' x)). Qed.
Lemma lem8009344 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8009345 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term435 _142062 _142063 _142064 s s' t t' x) = (term436 _142062 _142063 _142064 x s s' t t').
Proof. exact (MK_COMB (@lem8009344) (@lem8009343 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009346 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term430 _142062 _142063 _142064 s s' t t' x) = (term416 _142062 _142063 _142064 x s s' t t').
Proof. exact (eq_refl (term430 _142062 _142063 _142064 s s' t t' x)). Qed.
Lemma lem8009347 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term437 _142062 _142063 _142064 s s' t t' x) = (term438 _142062 _142063 _142064 x s s' t t').
Proof. exact (MK_COMB (@lem8009345 _142062 _142063 _142064 x s s' t t') (@lem8009346 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009348 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term439 _142062 _142063 _142064 s s' t t') = (term440 _142062 _142063 _142064 s s' t t').
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8009347 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009349 {_142062 _142063 : Type'} : (@ex (cart _142062 _142063)) = (@ex (cart _142062 _142063)).
Proof. exact (eq_refl (@ex (cart _142062 _142063))). Qed.
Lemma lem8009350 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term425 _142062 _142063 _142064 s s' t t') = (term441 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009349 _142062 _142063) (@lem8009348 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009351 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : ((term424 _142062 _142063 _142064 s s' t t') = (term425 _142062 _142063 _142064 s s' t t')) = ((term419 _142062 _142063 _142064 s s' t t') = (term441 _142062 _142063 _142064 s s' t t')).
Proof. exact (MK_COMB (@lem8009342 _142062 _142063 _142064 s s' t t') (@lem8009350 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009352 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term419 _142062 _142063 _142064 s s' t t') = (term441 _142062 _142063 _142064 s s' t t').
Proof. exact (EQ_MP (@lem8009351 _142062 _142063 _142064 s s' t t') (@lem8009329 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009354 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term420 A P Q) = (term421 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem8009355 {_142062 _142064 : Type'} (P : type24 _142062 _142064) (Q : type24 _142062 _142064) : (term422 _142062 _142064 P Q) = (term423 _142062 _142064 P Q).
Proof. exact (@lem8009354 (cart _142062 _142064) P Q). Qed.
Lemma lem8009356 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term442 _142062 _142063 _142064 x s s' t t') = (term443 _142062 _142063 _142064 x s s' t t').
Proof. exact (@lem8009355 _142062 _142064 (term382 _142062 _142063 _142064 x s s' t t') (term415 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009357 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term444 _142062 _142063 _142064 x s s' t t' y) = (term381 _142062 _142063 _142064 x y s s' t t').
Proof. exact (eq_refl (term444 _142062 _142063 _142064 x s s' t t' y)). Qed.
Lemma lem8009358 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term445 _142062 _142063 _142064 x s s' t t') = (term382 _142062 _142063 _142064 x s s' t t').
Proof. exact (fun_ext (fun y : cart _142062 _142064 => @lem8009357 _142062 _142063 _142064 x y s s' t t')). Qed.
Lemma lem8009359 {_142062 _142064 : Type'} : (@ex (cart _142062 _142064)) = (@ex (cart _142062 _142064)).
Proof. exact (eq_refl (@ex (cart _142062 _142064))). Qed.
Lemma lem8009360 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term446 _142062 _142063 _142064 x s s' t t') = (term383 _142062 _142063 _142064 x s s' t t').
Proof. exact (MK_COMB (@lem8009359 _142062 _142064) (@lem8009358 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009361 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8009362 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term447 _142062 _142063 _142064 x s s' t t') = (term436 _142062 _142063 _142064 x s s' t t').
Proof. exact (MK_COMB (@lem8009361) (@lem8009360 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009363 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term448 _142062 _142063 _142064 x s s' t t' y) = (term413 _142062 _142063 _142064 x y s s' t t').
Proof. exact (eq_refl (term448 _142062 _142063 _142064 x s s' t t' y)). Qed.
Lemma lem8009364 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term449 _142062 _142063 _142064 x s s' t t') = (term415 _142062 _142063 _142064 x s s' t t').
Proof. exact (fun_ext (fun y : cart _142062 _142064 => @lem8009363 _142062 _142063 _142064 x y s s' t t')). Qed.
Lemma lem8009365 {_142062 _142064 : Type'} : (@ex (cart _142062 _142064)) = (@ex (cart _142062 _142064)).
Proof. exact (eq_refl (@ex (cart _142062 _142064))). Qed.
Lemma lem8009366 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term450 _142062 _142063 _142064 x s s' t t') = (term416 _142062 _142063 _142064 x s s' t t').
Proof. exact (MK_COMB (@lem8009365 _142062 _142064) (@lem8009364 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009367 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term442 _142062 _142063 _142064 x s s' t t') = (term438 _142062 _142063 _142064 x s s' t t').
Proof. exact (MK_COMB (@lem8009362 _142062 _142063 _142064 x s s' t t') (@lem8009366 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009368 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8009369 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term451 _142062 _142063 _142064 x s s' t t') = (term452 _142062 _142063 _142064 x s s' t t').
Proof. exact (MK_COMB (@lem8009368) (@lem8009367 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009370 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term444 _142062 _142063 _142064 x s s' t t' y) = (term381 _142062 _142063 _142064 x y s s' t t').
Proof. exact (eq_refl (term444 _142062 _142063 _142064 x s s' t t' y)). Qed.
Lemma lem8009371 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8009372 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term453 _142062 _142063 _142064 x s s' t t' y) = (term454 _142062 _142063 _142064 x y s s' t t').
Proof. exact (MK_COMB (@lem8009371) (@lem8009370 _142062 _142063 _142064 x y s s' t t')). Qed.
Lemma lem8009373 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term448 _142062 _142063 _142064 x s s' t t' y) = (term413 _142062 _142063 _142064 x y s s' t t').
Proof. exact (eq_refl (term448 _142062 _142063 _142064 x s s' t t' y)). Qed.
Lemma lem8009374 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term455 _142062 _142063 _142064 x s s' t t' y) = (term456 _142062 _142063 _142064 x y s s' t t').
Proof. exact (MK_COMB (@lem8009372 _142062 _142063 _142064 x y s s' t t') (@lem8009373 _142062 _142063 _142064 x y s s' t t')). Qed.
Lemma lem8009375 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term457 _142062 _142063 _142064 x s s' t t') = (term458 _142062 _142063 _142064 x s s' t t').
Proof. exact (fun_ext (fun y : cart _142062 _142064 => @lem8009374 _142062 _142063 _142064 x y s s' t t')). Qed.
Lemma lem8009376 {_142062 _142064 : Type'} : (@ex (cart _142062 _142064)) = (@ex (cart _142062 _142064)).
Proof. exact (eq_refl (@ex (cart _142062 _142064))). Qed.
Lemma lem8009377 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term443 _142062 _142063 _142064 x s s' t t') = (term459 _142062 _142063 _142064 x s s' t t').
Proof. exact (MK_COMB (@lem8009376 _142062 _142064) (@lem8009375 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009378 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : ((term442 _142062 _142063 _142064 x s s' t t') = (term443 _142062 _142063 _142064 x s s' t t')) = ((term438 _142062 _142063 _142064 x s s' t t') = (term459 _142062 _142063 _142064 x s s' t t')).
Proof. exact (MK_COMB (@lem8009369 _142062 _142063 _142064 x s s' t t') (@lem8009377 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009379 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term438 _142062 _142063 _142064 x s s' t t') = (term459 _142062 _142063 _142064 x s s' t t').
Proof. exact (EQ_MP (@lem8009378 _142062 _142063 _142064 x s s' t t') (@lem8009356 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009382 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term460 _142062 _142063 _142064 x s s' t t') = (term460 _142062 _142063 _142064 x s s' t t').
Proof. exact (eq_refl (term460 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009383 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term460 _142062 _142063 _142064 x s s' t t') = ((term438 _142062 _142063 _142064 x s s' t t') = (term459 _142062 _142063 _142064 x s s' t t')).
Proof. exact (eq_refl (term460 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009384 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term461 _142062 _142063 _142064 x s s' t t') = (term461 _142062 _142063 _142064 x s s' t t').
Proof. exact (eq_refl (term461 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009385 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : ((term460 _142062 _142063 _142064 x s s' t t') = (term460 _142062 _142063 _142064 x s s' t t')) = ((term460 _142062 _142063 _142064 x s s' t t') = ((term438 _142062 _142063 _142064 x s s' t t') = (term459 _142062 _142063 _142064 x s s' t t'))).
Proof. exact (MK_COMB (@lem8009384 _142062 _142063 _142064 x s s' t t') (@lem8009383 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009386 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term460 _142062 _142063 _142064 x s s' t t') = ((term438 _142062 _142063 _142064 x s s' t t') = (term459 _142062 _142063 _142064 x s s' t t')).
Proof. exact (eq_refl (term460 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009387 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8009388 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term461 _142062 _142063 _142064 x s s' t t') = (term462 _142062 _142063 _142064 x s s' t t').
Proof. exact (MK_COMB (@lem8009387) (@lem8009386 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009389 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : ((term438 _142062 _142063 _142064 x s s' t t') = (term459 _142062 _142063 _142064 x s s' t t')) = ((term438 _142062 _142063 _142064 x s s' t t') = (term459 _142062 _142063 _142064 x s s' t t')).
Proof. exact (eq_refl ((term438 _142062 _142063 _142064 x s s' t t') = (term459 _142062 _142063 _142064 x s s' t t'))). Qed.
Lemma lem8009390 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : ((term460 _142062 _142063 _142064 x s s' t t') = ((term438 _142062 _142063 _142064 x s s' t t') = (term459 _142062 _142063 _142064 x s s' t t'))) = (((term438 _142062 _142063 _142064 x s s' t t') = (term459 _142062 _142063 _142064 x s s' t t')) = ((term438 _142062 _142063 _142064 x s s' t t') = (term459 _142062 _142063 _142064 x s s' t t'))).
Proof. exact (MK_COMB (@lem8009388 _142062 _142063 _142064 x s s' t t') (@lem8009389 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009391 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : ((term460 _142062 _142063 _142064 x s s' t t') = (term460 _142062 _142063 _142064 x s s' t t')) = (((term438 _142062 _142063 _142064 x s s' t t') = (term459 _142062 _142063 _142064 x s s' t t')) = ((term438 _142062 _142063 _142064 x s s' t t') = (term459 _142062 _142063 _142064 x s s' t t'))).
Proof. exact (TRANS (@lem8009385 _142062 _142063 _142064 x s s' t t') (@lem8009390 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009392 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : ((term438 _142062 _142063 _142064 x s s' t t') = (term459 _142062 _142063 _142064 x s s' t t')) = ((term438 _142062 _142063 _142064 x s s' t t') = (term459 _142062 _142063 _142064 x s s' t t')).
Proof. exact (EQ_MP (@lem8009391 _142062 _142063 _142064 x s s' t t') (@lem8009382 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009393 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term438 _142062 _142063 _142064 x s s' t t') = (term459 _142062 _142063 _142064 x s s' t t').
Proof. exact (EQ_MP (@lem8009392 _142062 _142063 _142064 x s s' t t') (@lem8009379 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009395 {A : Type'} (P : A -> Prop) (Q : Prop) : (term193 A P Q) = (term194 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem8009396 {_142062 _142063 : Type'} (P : type24 _142062 _142063) (Q : Prop) : (term195 _142062 _142063 P Q) = (term196 _142062 _142063 P Q).
Proof. exact (@lem8009395 (cart _142062 _142063) P Q). Qed.
Lemma lem8009397 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term463 _142062 _142063 _142064 x y s s' t t') = (term464 _142062 _142063 _142064 x y s s' t t').
Proof. exact (@lem8009396 _142062 _142063 (term380 _142062 _142063 _142064 x y s s' t t') (term413 _142062 _142063 _142064 x y s s' t t')). Qed.
Lemma lem8009398 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term465 _142062 _142063 _142064 x y s s' t t' x') = (term379 _142062 _142063 _142064 x y s x' s' t t').
Proof. exact (eq_refl (term465 _142062 _142063 _142064 x y s s' t t' x')). Qed.
Lemma lem8009399 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term466 _142062 _142063 _142064 x y s s' t t') = (term380 _142062 _142063 _142064 x y s s' t t').
Proof. exact (fun_ext (fun x' : cart _142062 _142063 => @lem8009398 _142062 _142063 _142064 x y s x' s' t t')). Qed.
Lemma lem8009400 {_142062 _142063 : Type'} : (@ex (cart _142062 _142063)) = (@ex (cart _142062 _142063)).
Proof. exact (eq_refl (@ex (cart _142062 _142063))). Qed.
Lemma lem8009401 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term467 _142062 _142063 _142064 x y s s' t t') = (term381 _142062 _142063 _142064 x y s s' t t').
Proof. exact (MK_COMB (@lem8009400 _142062 _142063) (@lem8009399 _142062 _142063 _142064 x y s s' t t')). Qed.
Lemma lem8009402 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8009403 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term468 _142062 _142063 _142064 x y s s' t t') = (term454 _142062 _142063 _142064 x y s s' t t').
Proof. exact (MK_COMB (@lem8009402) (@lem8009401 _142062 _142063 _142064 x y s s' t t')). Qed.
Lemma lem8009404 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term413 _142062 _142063 _142064 x y s s' t t') = (term413 _142062 _142063 _142064 x y s s' t t').
Proof. exact (eq_refl (term413 _142062 _142063 _142064 x y s s' t t')). Qed.
Lemma lem8009405 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term463 _142062 _142063 _142064 x y s s' t t') = (term456 _142062 _142063 _142064 x y s s' t t').
Proof. exact (MK_COMB (@lem8009403 _142062 _142063 _142064 x y s s' t t') (@lem8009404 _142062 _142063 _142064 x y s s' t t')). Qed.
Lemma lem8009406 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8009407 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term469 _142062 _142063 _142064 x y s s' t t') = (term470 _142062 _142063 _142064 x y s s' t t').
Proof. exact (MK_COMB (@lem8009406) (@lem8009405 _142062 _142063 _142064 x y s s' t t')). Qed.
Lemma lem8009408 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term465 _142062 _142063 _142064 x y s s' t t' x') = (term379 _142062 _142063 _142064 x y s x' s' t t').
Proof. exact (eq_refl (term465 _142062 _142063 _142064 x y s s' t t' x')). Qed.
Lemma lem8009409 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8009410 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term471 _142062 _142063 _142064 x y s s' t t' x') = (term472 _142062 _142063 _142064 x y s x' s' t t').
Proof. exact (MK_COMB (@lem8009409) (@lem8009408 _142062 _142063 _142064 x y s x' s' t t')). Qed.
Lemma lem8009411 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term413 _142062 _142063 _142064 x y s s' t t') = (term413 _142062 _142063 _142064 x y s s' t t').
Proof. exact (eq_refl (term413 _142062 _142063 _142064 x y s s' t t')). Qed.
Lemma lem8009412 {_142062 _142063 _142064 : Type'} (x' : cart _142062 _142063) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term473 _142062 _142063 _142064 x' x y s s' t t') = (term474 _142062 _142063 _142064 x' x y s s' t t').
Proof. exact (MK_COMB (@lem8009410 _142062 _142063 _142064 x y s x' s' t t') (@lem8009411 _142062 _142063 _142064 x y s s' t t')). Qed.
Lemma lem8009413 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term475 _142062 _142063 _142064 x y s s' t t') = (term476 _142062 _142063 _142064 x y s s' t t').
Proof. exact (fun_ext (fun x' : cart _142062 _142063 => @lem8009412 _142062 _142063 _142064 x' x y s s' t t')). Qed.
Lemma lem8009414 {_142062 _142063 : Type'} : (@ex (cart _142062 _142063)) = (@ex (cart _142062 _142063)).
Proof. exact (eq_refl (@ex (cart _142062 _142063))). Qed.
Lemma lem8009415 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term464 _142062 _142063 _142064 x y s s' t t') = (term477 _142062 _142063 _142064 x y s s' t t').
Proof. exact (MK_COMB (@lem8009414 _142062 _142063) (@lem8009413 _142062 _142063 _142064 x y s s' t t')). Qed.
Lemma lem8009416 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : ((term463 _142062 _142063 _142064 x y s s' t t') = (term464 _142062 _142063 _142064 x y s s' t t')) = ((term456 _142062 _142063 _142064 x y s s' t t') = (term477 _142062 _142063 _142064 x y s s' t t')).
Proof. exact (MK_COMB (@lem8009407 _142062 _142063 _142064 x y s s' t t') (@lem8009415 _142062 _142063 _142064 x y s s' t t')). Qed.
Lemma lem8009417 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term456 _142062 _142063 _142064 x y s s' t t') = (term477 _142062 _142063 _142064 x y s s' t t').
Proof. exact (EQ_MP (@lem8009416 _142062 _142063 _142064 x y s s' t t') (@lem8009397 _142062 _142063 _142064 x y s s' t t')). Qed.
Lemma lem8009419 {A : Type'} (P : A -> Prop) (Q : Prop) : (term193 A P Q) = (term194 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem8009420 {_142062 _142064 : Type'} (P : type24 _142062 _142064) (Q : Prop) : (term195 _142062 _142064 P Q) = (term196 _142062 _142064 P Q).
Proof. exact (@lem8009419 (cart _142062 _142064) P Q). Qed.
Lemma lem8009421 {_142062 _142063 _142064 : Type'} (x' : cart _142062 _142063) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term478 _142062 _142063 _142064 x' x y s s' t t') = (term479 _142062 _142063 _142064 x' x y s s' t t').
Proof. exact (@lem8009420 _142062 _142064 (term378 _142062 _142063 _142064 x y s x' s' t t') (term413 _142062 _142063 _142064 x y s s' t t')). Qed.
Lemma lem8009422 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) : (term480 _142062 _142063 _142064 x y s x' s' t t' x'') = (term376 _142062 _142063 _142064 x y s x' s' t x'' t').
Proof. exact (eq_refl (term480 _142062 _142063 _142064 x y s x' s' t t' x'')). Qed.
Lemma lem8009423 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term481 _142062 _142063 _142064 x y s x' s' t t') = (term378 _142062 _142063 _142064 x y s x' s' t t').
Proof. exact (fun_ext (fun x'' : cart _142062 _142064 => @lem8009422 _142062 _142063 _142064 x y s x' s' t x'' t')). Qed.
Lemma lem8009424 {_142062 _142064 : Type'} : (@ex (cart _142062 _142064)) = (@ex (cart _142062 _142064)).
Proof. exact (eq_refl (@ex (cart _142062 _142064))). Qed.
Lemma lem8009425 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term482 _142062 _142063 _142064 x y s x' s' t t') = (term379 _142062 _142063 _142064 x y s x' s' t t').
Proof. exact (MK_COMB (@lem8009424 _142062 _142064) (@lem8009423 _142062 _142063 _142064 x y s x' s' t t')). Qed.
Lemma lem8009426 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8009427 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term483 _142062 _142063 _142064 x y s x' s' t t') = (term472 _142062 _142063 _142064 x y s x' s' t t').
Proof. exact (MK_COMB (@lem8009426) (@lem8009425 _142062 _142063 _142064 x y s x' s' t t')). Qed.
Lemma lem8009428 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term413 _142062 _142063 _142064 x y s s' t t') = (term413 _142062 _142063 _142064 x y s s' t t').
Proof. exact (eq_refl (term413 _142062 _142063 _142064 x y s s' t t')). Qed.
Lemma lem8009429 {_142062 _142063 _142064 : Type'} (x' : cart _142062 _142063) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term478 _142062 _142063 _142064 x' x y s s' t t') = (term474 _142062 _142063 _142064 x' x y s s' t t').
Proof. exact (MK_COMB (@lem8009427 _142062 _142063 _142064 x y s x' s' t t') (@lem8009428 _142062 _142063 _142064 x y s s' t t')). Qed.
Lemma lem8009430 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8009431 {_142062 _142063 _142064 : Type'} (x' : cart _142062 _142063) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term484 _142062 _142063 _142064 x' x y s s' t t') = (term485 _142062 _142063 _142064 x' x y s s' t t').
Proof. exact (MK_COMB (@lem8009430) (@lem8009429 _142062 _142063 _142064 x' x y s s' t t')). Qed.
Lemma lem8009432 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) : (term480 _142062 _142063 _142064 x y s x' s' t t' x'') = (term376 _142062 _142063 _142064 x y s x' s' t x'' t').
Proof. exact (eq_refl (term480 _142062 _142063 _142064 x y s x' s' t t' x'')). Qed.
Lemma lem8009433 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8009434 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) : (term486 _142062 _142063 _142064 x y s x' s' t t' x'') = (term487 _142062 _142063 _142064 x y s x' s' t x'' t').
Proof. exact (MK_COMB (@lem8009433) (@lem8009432 _142062 _142063 _142064 x y s x' s' t x'' t')). Qed.
Lemma lem8009435 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term413 _142062 _142063 _142064 x y s s' t t') = (term413 _142062 _142063 _142064 x y s s' t t').
Proof. exact (eq_refl (term413 _142062 _142063 _142064 x y s s' t t')). Qed.
Lemma lem8009436 {_142062 _142063 _142064 : Type'} (x' : cart _142062 _142063) (x'' : cart _142062 _142064) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term488 _142062 _142063 _142064 x' x'' x y s s' t t') = (term489 _142062 _142063 _142064 x' x'' x y s s' t t').
Proof. exact (MK_COMB (@lem8009434 _142062 _142063 _142064 x y s x' s' t x'' t') (@lem8009435 _142062 _142063 _142064 x y s s' t t')). Qed.
Lemma lem8009437 {_142062 _142063 _142064 : Type'} (x' : cart _142062 _142063) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term490 _142062 _142063 _142064 x' x y s s' t t') = (term491 _142062 _142063 _142064 x' x y s s' t t').
Proof. exact (fun_ext (fun x'' : cart _142062 _142064 => @lem8009436 _142062 _142063 _142064 x' x'' x y s s' t t')). Qed.
Lemma lem8009438 {_142062 _142064 : Type'} : (@ex (cart _142062 _142064)) = (@ex (cart _142062 _142064)).
Proof. exact (eq_refl (@ex (cart _142062 _142064))). Qed.
Lemma lem8009439 {_142062 _142063 _142064 : Type'} (x' : cart _142062 _142063) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term479 _142062 _142063 _142064 x' x y s s' t t') = (term492 _142062 _142063 _142064 x' x y s s' t t').
Proof. exact (MK_COMB (@lem8009438 _142062 _142064) (@lem8009437 _142062 _142063 _142064 x' x y s s' t t')). Qed.
Lemma lem8009440 {_142062 _142063 _142064 : Type'} (x' : cart _142062 _142063) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : ((term478 _142062 _142063 _142064 x' x y s s' t t') = (term479 _142062 _142063 _142064 x' x y s s' t t')) = ((term474 _142062 _142063 _142064 x' x y s s' t t') = (term492 _142062 _142063 _142064 x' x y s s' t t')).
Proof. exact (MK_COMB (@lem8009431 _142062 _142063 _142064 x' x y s s' t t') (@lem8009439 _142062 _142063 _142064 x' x y s s' t t')). Qed.
Lemma lem8009441 {_142062 _142063 _142064 : Type'} (x' : cart _142062 _142063) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term474 _142062 _142063 _142064 x' x y s s' t t') = (term492 _142062 _142063 _142064 x' x y s s' t t').
Proof. exact (EQ_MP (@lem8009440 _142062 _142063 _142064 x' x y s s' t t') (@lem8009421 _142062 _142063 _142064 x' x y s s' t t')). Qed.
Lemma lem8009442 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term476 _142062 _142063 _142064 x y s s' t t') = (term493 _142062 _142063 _142064 x y s s' t t').
Proof. exact (fun_ext (fun x' : cart _142062 _142063 => @lem8009441 _142062 _142063 _142064 x' x y s s' t t')). Qed.
Lemma lem8009443 {_142062 _142063 : Type'} : (@ex (cart _142062 _142063)) = (@ex (cart _142062 _142063)).
Proof. exact (eq_refl (@ex (cart _142062 _142063))). Qed.
Lemma lem8009444 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term477 _142062 _142063 _142064 x y s s' t t') = (term494 _142062 _142063 _142064 x y s s' t t').
Proof. exact (MK_COMB (@lem8009443 _142062 _142063) (@lem8009442 _142062 _142063 _142064 x y s s' t t')). Qed.
Lemma lem8009445 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term456 _142062 _142063 _142064 x y s s' t t') = (term494 _142062 _142063 _142064 x y s s' t t').
Proof. exact (TRANS (@lem8009417 _142062 _142063 _142064 x y s s' t t') (@lem8009444 _142062 _142063 _142064 x y s s' t t')). Qed.
Lemma lem8009446 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term458 _142062 _142063 _142064 x s s' t t') = (term495 _142062 _142063 _142064 x s s' t t').
Proof. exact (fun_ext (fun y : cart _142062 _142064 => @lem8009445 _142062 _142063 _142064 x y s s' t t')). Qed.
Lemma lem8009447 {_142062 _142064 : Type'} : (@ex (cart _142062 _142064)) = (@ex (cart _142062 _142064)).
Proof. exact (eq_refl (@ex (cart _142062 _142064))). Qed.
Lemma lem8009448 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term459 _142062 _142063 _142064 x s s' t t') = (term496 _142062 _142063 _142064 x s s' t t').
Proof. exact (MK_COMB (@lem8009447 _142062 _142064) (@lem8009446 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009449 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term438 _142062 _142063 _142064 x s s' t t') = (term496 _142062 _142063 _142064 x s s' t t').
Proof. exact (TRANS (@lem8009393 _142062 _142063 _142064 x s s' t t') (@lem8009448 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009450 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term440 _142062 _142063 _142064 s s' t t') = (term497 _142062 _142063 _142064 s s' t t').
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8009449 _142062 _142063 _142064 x s s' t t')). Qed.
Lemma lem8009451 {_142062 _142063 : Type'} : (@ex (cart _142062 _142063)) = (@ex (cart _142062 _142063)).
Proof. exact (eq_refl (@ex (cart _142062 _142063))). Qed.
Lemma lem8009452 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term441 _142062 _142063 _142064 s s' t t') = (term498 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009451 _142062 _142063) (@lem8009450 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009453 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term419 _142062 _142063 _142064 s s' t t') = (term498 _142062 _142063 _142064 s s' t t').
Proof. exact (TRANS (@lem8009352 _142062 _142063 _142064 s s' t t') (@lem8009452 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009455 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term192 _142062 _142063 _142064 s s' t t') = (term498 _142062 _142063 _142064 s s' t t').
Proof. exact (TRANS (@lem8009325 _142062 _142063 _142064 s s' t t') (@lem8009453 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009456 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term113 _142062 _142063 _142064 s s' t t') = (term498 _142062 _142063 _142064 s s' t t').
Proof. exact (TRANS (@lem8008638 _142062 _142063 _142064 s s' t t') (@lem8009455 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009457 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term113 _142062 _142063 _142064 s s' t t') : term498 _142062 _142063 _142064 s s' t t'.
Proof. exact (EQ_MP (@lem8009456 _142062 _142063 _142064 s s' t t') (@lem8008455 _142062 _142063 _142064 s s' t t' h1)). Qed.
Lemma lem8009458 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term496 _142062 _142063 _142064 x s s' t t') : term496 _142062 _142063 _142064 x s s' t t'.
Proof. exact (h1). Qed.
Lemma lem8009459 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term494 _142062 _142063 _142064 x y s s' t t') : term494 _142062 _142063 _142064 x y s s' t t'.
Proof. exact (h1). Qed.
Lemma lem8009460 {_142062 _142063 _142064 : Type'} (x' : cart _142062 _142063) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term492 _142062 _142063 _142064 x' x y s s' t t') : term492 _142062 _142063 _142064 x' x y s s' t t'.
Proof. exact (h1). Qed.
Lemma lem8009461 {_142062 _142063 _142064 : Type'} (x' : cart _142062 _142063) (x'' : cart _142062 _142064) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term489 _142062 _142063 _142064 x' x'' x y s s' t t') : term489 _142062 _142063 _142064 x' x'' x y s s' t t'.
Proof. exact (h1). Qed.
Lemma lem8009476 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (x : cart _142062 _142064) (t' : type24 _142062 _142064) : (term154 _142062 _142064 t x t') = (term154 _142062 _142064 t x t').
Proof. exact (eq_refl (term154 _142062 _142064 t x t')). Qed.
Lemma lem8009477 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term162 _142062 _142064 t t') = (term162 _142062 _142064 t t').
Proof. exact (fun_ext (fun x : cart _142062 _142064 => @lem8009476 _142062 _142064 t x t')). Qed.
Lemma lem8009478 {_142062 _142064 : Type'} : (@all (cart _142062 _142064)) = (@all (cart _142062 _142064)).
Proof. exact (eq_refl (@all (cart _142062 _142064))). Qed.
Lemma lem8009479 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term163 _142062 _142064 t t') = (term163 _142062 _142064 t t').
Proof. exact (MK_COMB (@lem8009478 _142062 _142064) (@lem8009477 _142062 _142064 t t')). Qed.
Lemma lem8009494 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (x : cart _142062 _142063) (s' : type24 _142062 _142063) : (term154 _142062 _142063 s x s') = (term154 _142062 _142063 s x s').
Proof. exact (eq_refl (term154 _142062 _142063 s x s')). Qed.
Lemma lem8009495 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) : (term162 _142062 _142063 s s') = (term162 _142062 _142063 s s').
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8009494 _142062 _142063 s x s')). Qed.
Lemma lem8009496 {_142062 _142063 : Type'} : (@all (cart _142062 _142063)) = (@all (cart _142062 _142063)).
Proof. exact (eq_refl (@all (cart _142062 _142063))). Qed.
Lemma lem8009497 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) : (term163 _142062 _142063 s s') = (term163 _142062 _142063 s s').
Proof. exact (MK_COMB (@lem8009496 _142062 _142063) (@lem8009495 _142062 _142063 s s')). Qed.
Lemma lem8009498 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8009499 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) : (term169 _142062 _142063 s s') = (term169 _142062 _142063 s s').
Proof. exact (MK_COMB (@lem8009498) (@lem8009497 _142062 _142063 s s')). Qed.
Lemma lem8009500 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term170 _142062 _142063 _142064 s s' t t') = (term170 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009499 _142062 _142063 s s') (@lem8009479 _142062 _142064 t t')). Qed.
Lemma lem8009507 {_142062 _142064 : Type'} (x : cart _142062 _142064) (t : type24 _142062 _142064) : (term71 _142062 _142064 x t) = (term71 _142062 _142064 x t).
Proof. exact (eq_refl (term71 _142062 _142064 x t)). Qed.
Lemma lem8009508 {_142062 _142064 : Type'} (t : type24 _142062 _142064) : (term73 _142062 _142064 t) = (term73 _142062 _142064 t).
Proof. exact (fun_ext (fun x : cart _142062 _142064 => @lem8009507 _142062 _142064 x t)). Qed.
Lemma lem8009509 {_142062 _142064 : Type'} : (@all (cart _142062 _142064)) = (@all (cart _142062 _142064)).
Proof. exact (eq_refl (@all (cart _142062 _142064))). Qed.
Lemma lem8009510 {_142062 _142064 : Type'} (t : type24 _142062 _142064) : (term74 _142062 _142064 t) = (term74 _142062 _142064 t).
Proof. exact (MK_COMB (@lem8009509 _142062 _142064) (@lem8009508 _142062 _142064 t)). Qed.
Lemma lem8009511 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8009512 {_142062 _142064 : Type'} (t : type24 _142062 _142064) : (term76 _142062 _142064 t) = (term76 _142062 _142064 t).
Proof. exact (MK_COMB (@lem8009511) (@lem8009510 _142062 _142064 t)). Qed.
Lemma lem8009513 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term176 _142062 _142063 _142064 s s' t t') = (term176 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009512 _142062 _142064 t) (@lem8009500 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009520 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) : (term71 _142062 _142063 x s) = (term71 _142062 _142063 x s).
Proof. exact (eq_refl (term71 _142062 _142063 x s)). Qed.
Lemma lem8009521 {_142062 _142063 : Type'} (s : type24 _142062 _142063) : (term73 _142062 _142063 s) = (term73 _142062 _142063 s).
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8009520 _142062 _142063 x s)). Qed.
Lemma lem8009522 {_142062 _142063 : Type'} : (@all (cart _142062 _142063)) = (@all (cart _142062 _142063)).
Proof. exact (eq_refl (@all (cart _142062 _142063))). Qed.
Lemma lem8009523 {_142062 _142063 : Type'} (s : type24 _142062 _142063) : (term74 _142062 _142063 s) = (term74 _142062 _142063 s).
Proof. exact (MK_COMB (@lem8009522 _142062 _142063) (@lem8009521 _142062 _142063 s)). Qed.
Lemma lem8009524 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8009525 {_142062 _142063 : Type'} (s : type24 _142062 _142063) : (term76 _142062 _142063 s) = (term76 _142062 _142063 s).
Proof. exact (MK_COMB (@lem8009524) (@lem8009523 _142062 _142063 s)). Qed.
Lemma lem8009526 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term180 _142062 _142063 _142064 s s' t t') = (term180 _142062 _142063 _142064 s s' t t').
Proof. exact (MK_COMB (@lem8009525 _142062 _142063 s) (@lem8009513 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009561 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (y : cart _142062 _142064) (t' : type24 _142062 _142064) : (term411 _142062 _142063 _142064 s t x s' y t') = (term411 _142062 _142063 _142064 s t x s' y t').
Proof. exact (eq_refl (term411 _142062 _142063 _142064 s t x s' y t')). Qed.
Lemma lem8009562 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term413 _142062 _142063 _142064 x y s s' t t') = (term413 _142062 _142063 _142064 x y s s' t t').
Proof. exact (MK_COMB (@lem8009561 _142062 _142063 _142064 s t x s' y t') (@lem8009526 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8009611 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) : (term321 _142062 _142063 _142064 x y s x' s' t x'' t') = (term321 _142062 _142063 _142064 x y s x' s' t x'' t').
Proof. exact (eq_refl (term321 _142062 _142063 _142064 x y s x' s' t x'' t')). Qed.
Lemma lem8009644 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (y : cart _142062 _142064) (t' : type24 _142062 _142064) : (term123 _142062 _142063 _142064 s t x s' y t') = (term123 _142062 _142063 _142064 s t x s' y t').
Proof. exact (eq_refl (term123 _142062 _142063 _142064 s t x s' y t')). Qed.
Lemma lem8009645 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term133 _142062 _142063 _142064 s t x s' t') = (term133 _142062 _142063 _142064 s t x s' t').
Proof. exact (fun_ext (fun y : cart _142062 _142064 => @lem8009644 _142062 _142063 _142064 s t x s' y t')). Qed.
Lemma lem8009646 {_142062 _142064 : Type'} : (@all (cart _142062 _142064)) = (@all (cart _142062 _142064)).
Proof. exact (eq_refl (@all (cart _142062 _142064))). Qed.
Lemma lem8009647 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (x : cart _142062 _142063) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term134 _142062 _142063 _142064 s t x s' t') = (term134 _142062 _142063 _142064 s t x s' t').
Proof. exact (MK_COMB (@lem8009646 _142062 _142064) (@lem8009645 _142062 _142063 _142064 s t x s' t')). Qed.
Lemma lem8009648 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term142 _142062 _142063 _142064 s t s' t') = (term142 _142062 _142063 _142064 s t s' t').
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8009647 _142062 _142063 _142064 s t x s' t')). Qed.
Lemma lem8009649 {_142062 _142063 : Type'} : (@all (cart _142062 _142063)) = (@all (cart _142062 _142063)).
Proof. exact (eq_refl (@all (cart _142062 _142063))). Qed.
Lemma lem8009650 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term143 _142062 _142063 _142064 s t s' t') = (term143 _142062 _142063 _142064 s t s' t').
Proof. exact (MK_COMB (@lem8009649 _142062 _142063) (@lem8009648 _142062 _142063 _142064 s t s' t')). Qed.
Lemma lem8009651 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8009652 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) (s' : type24 _142062 _142063) (t' : type24 _142062 _142064) : (term186 _142062 _142063 _142064 s t s' t') = (term186 _142062 _142063 _142064 s t s' t').
Proof. exact (MK_COMB (@lem8009651) (@lem8009650 _142062 _142063 _142064 s t s' t')). Qed.
Lemma lem8009653 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) : (term376 _142062 _142063 _142064 x y s x' s' t x'' t') = (term376 _142062 _142063 _142064 x y s x' s' t x'' t').
Proof. exact (MK_COMB (@lem8009652 _142062 _142063 _142064 s t s' t') (@lem8009611 _142062 _142063 _142064 x y s x' s' t x'' t')). Qed.
Lemma lem8009654 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8009655 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) : (term487 _142062 _142063 _142064 x y s x' s' t x'' t') = (term487 _142062 _142063 _142064 x y s x' s' t x'' t').
Proof. exact (MK_COMB (@lem8009654) (@lem8009653 _142062 _142063 _142064 x y s x' s' t x'' t')). Qed.
Lemma lem8009656 {_142062 _142063 _142064 : Type'} (x' : cart _142062 _142063) (x'' : cart _142062 _142064) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term489 _142062 _142063 _142064 x' x'' x y s s' t t') = (term489 _142062 _142063 _142064 x' x'' x y s s' t t').
Proof. exact (MK_COMB (@lem8009655 _142062 _142063 _142064 x y s x' s' t x'' t') (@lem8009562 _142062 _142063 _142064 x y s s' t t')). Qed.
Lemma lem8009657 {_142062 _142063 _142064 : Type'} (x' : cart _142062 _142063) (x'' : cart _142062 _142064) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term489 _142062 _142063 _142064 x' x'' x y s s' t t') : term489 _142062 _142063 _142064 x' x'' x y s s' t t'.
Proof. exact (EQ_MP (@lem8009656 _142062 _142063 _142064 x' x'' x y s s' t t') (@lem8009461 _142062 _142063 _142064 x' x'' x y s s' t t' h1)). Qed.
Lemma lem8009658 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : term376 _142062 _142063 _142064 x y s x' s' t x'' t'.
Proof. exact (h1). Qed.
Lemma lem8009659 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term413 _142062 _142063 _142064 x y s s' t t') : term413 _142062 _142063 _142064 x y s s' t t'.
Proof. exact (h1). Qed.
Lemma lem8009660 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : term321 _142062 _142063 _142064 x y s x' s' t x'' t'.
Proof. exact (proj2 (@lem8009658 _142062 _142063 _142064 x y s x' s' t x'' t' h1)). Qed.
Lemma lem8009661 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : term143 _142062 _142063 _142064 s t s' t'.
Proof. exact (proj1 (@lem8009658 _142062 _142063 _142064 x y s x' s' t x'' t' h1)). Qed.
Lemma lem8009662 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : term271 _142062 _142063 _142064 y s x' s' t x'' t'.
Proof. exact (proj2 (@lem8009660 _142062 _142063 _142064 x y s x' s' t x'' t' h1)). Qed.
Lemma lem8009664 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : term221 _142062 _142063 _142064 s x' s' t x'' t'.
Proof. exact (proj2 (@lem8009662 _142062 _142063 _142064 x y s x' s' t x'' t' h1)). Qed.
Lemma lem8009666 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (h1 : term153 _142062 _142063 s x' s') : term153 _142062 _142063 s x' s'.
Proof. exact (h1). Qed.
Lemma lem8009667 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term153 _142062 _142064 t x'' t') : term153 _142062 _142064 t x'' t'.
Proof. exact (h1). Qed.
Lemma lem8009672 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term413 _142062 _142063 _142064 x y s s' t t') : term180 _142062 _142063 _142064 s s' t t'.
Proof. exact (proj2 (@lem8009659 _142062 _142063 _142064 x y s s' t t' h1)). Qed.
Lemma lem8009673 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term413 _142062 _142063 _142064 x y s s' t t') : term118 _142062 _142063 _142064 s t x s' y t'.
Proof. exact (proj1 (@lem8009659 _142062 _142063 _142064 x y s s' t t' h1)). Qed.
Lemma lem8009674 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term413 _142062 _142063 _142064 x y s s' t t') : term115 _142062 _142063 _142064 x s' y t'.
Proof. exact (proj2 (@lem8009673 _142062 _142063 _142064 x y s s' t t' h1)). Qed.
Lemma lem8009675 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term413 _142062 _142063 _142064 x y s s' t t') : term18 _142062 _142063 _142064 x s y t.
Proof. exact (proj1 (@lem8009673 _142062 _142063 _142064 x y s s' t t' h1)). Qed.
Lemma lem8009680 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (h1 : term74 _142062 _142063 s) : term74 _142062 _142063 s.
Proof. exact (h1). Qed.
Lemma lem8009681 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term176 _142062 _142063 _142064 s s' t t') : term176 _142062 _142063 _142064 s s' t t'.
Proof. exact (h1). Qed.
Lemma lem8009682 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (h1 : term74 _142062 _142064 t) : term74 _142062 _142064 t.
Proof. exact (h1). Qed.
Lemma lem8009683 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term170 _142062 _142063 _142064 s s' t t') : term170 _142062 _142063 _142064 s s' t t'.
Proof. exact (h1). Qed.
Lemma lem8009685 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term170 _142062 _142063 _142064 s s' t t') : term163 _142062 _142063 s s'.
Proof. exact (proj1 (@lem8009683 _142062 _142063 _142064 s s' t t' h1)). Qed.
Lemma lem8009686 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (h1 : term74 _142062 _142063 s) : term74 _142062 _142063 s.
Proof. exact (h1). Qed.
Lemma lem8009687 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term176 _142062 _142063 _142064 s s' t t') : term176 _142062 _142063 _142064 s s' t t'.
Proof. exact (h1). Qed.
Lemma lem8009688 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (h1 : term74 _142062 _142064 t) : term74 _142062 _142064 t.
Proof. exact (h1). Qed.
Lemma lem8009689 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term170 _142062 _142063 _142064 s s' t t') : term170 _142062 _142063 _142064 s s' t t'.
Proof. exact (h1). Qed.
Lemma lem8009690 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term170 _142062 _142063 _142064 s s' t t') : term163 _142062 _142064 t t'.
Proof. exact (proj2 (@lem8009689 _142062 _142063 _142064 s s' t t' h1)). Qed.
Lemma lem8009715 {_142062 _142063 _142064 : Type'} (s' : type24 _142062 _142063) (x : cart _142062 _142063) (s : type24 _142062 _142063) (t : type24 _142062 _142064) (y : cart _142062 _142064) (t' : type24 _142062 _142064) : (term123 _142062 _142063 _142064 s t x s' y t') = (term499 _142062 _142063 _142064 s' x s t y t').
Proof. exact (@lem19490 (@IN (cart _142062 _142063) x s') (term115 _142062 _142063 _142064 x s y t) (@IN (cart _142062 _142064) y t')). Qed.
Lemma lem8009716 {_142062 _142063 _142064 : Type'} (s' : type24 _142062 _142063) (x : cart _142062 _142063) (s : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term133 _142062 _142063 _142064 s t x s' t') = (term500 _142062 _142063 _142064 s' x s t t').
Proof. exact (fun_ext (fun y : cart _142062 _142064 => @lem8009715 _142062 _142063 _142064 s' x s t y t')). Qed.
Lemma lem8009717 {_142062 _142064 : Type'} : (@all (cart _142062 _142064)) = (@all (cart _142062 _142064)).
Proof. exact (eq_refl (@all (cart _142062 _142064))). Qed.
Lemma lem8009718 {_142062 _142063 _142064 : Type'} (s' : type24 _142062 _142063) (x : cart _142062 _142063) (s : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term134 _142062 _142063 _142064 s t x s' t') = (term501 _142062 _142063 _142064 s' x s t t').
Proof. exact (MK_COMB (@lem8009717 _142062 _142064) (@lem8009716 _142062 _142063 _142064 s' x s t t')). Qed.
Lemma lem8009719 {_142062 _142063 _142064 : Type'} (s' : type24 _142062 _142063) (s : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term142 _142062 _142063 _142064 s t s' t') = (term502 _142062 _142063 _142064 s' s t t').
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8009718 _142062 _142063 _142064 s' x s t t')). Qed.
Lemma lem8009720 {_142062 _142063 : Type'} : (@all (cart _142062 _142063)) = (@all (cart _142062 _142063)).
Proof. exact (eq_refl (@all (cart _142062 _142063))). Qed.
Lemma lem8009722 {_142062 _142063 _142064 : Type'} (s' : type24 _142062 _142063) (s : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term143 _142062 _142063 _142064 s t s' t') = (term503 _142062 _142063 _142064 s' s t t').
Proof. exact (MK_COMB (@lem8009720 _142062 _142063) (@lem8009719 _142062 _142063 _142064 s' s t t')). Qed.
Lemma lem8009723 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : term503 _142062 _142063 _142064 s' s t t'.
Proof. exact (EQ_MP (@lem8009722 _142062 _142063 _142064 s' s t t') (@lem8009661 _142062 _142063 _142064 x y s x' s' t x'' t' h1)). Qed.
Lemma lem8009763 {_142062 _142063 _142064 : Type'} (s' : type24 _142062 _142063) (x : cart _142062 _142063) (s : type24 _142062 _142063) (t : type24 _142062 _142064) (y : cart _142062 _142064) (t' : type24 _142062 _142064) : (term123 _142062 _142063 _142064 s t x s' y t') = (term499 _142062 _142063 _142064 s' x s t y t').
Proof. exact (@lem19490 (@IN (cart _142062 _142063) x s') (term115 _142062 _142063 _142064 x s y t) (@IN (cart _142062 _142064) y t')). Qed.
Lemma lem8009764 {_142062 _142063 _142064 : Type'} (s' : type24 _142062 _142063) (x : cart _142062 _142063) (s : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term133 _142062 _142063 _142064 s t x s' t') = (term500 _142062 _142063 _142064 s' x s t t').
Proof. exact (fun_ext (fun y : cart _142062 _142064 => @lem8009763 _142062 _142063 _142064 s' x s t y t')). Qed.
Lemma lem8009765 {_142062 _142064 : Type'} : (@all (cart _142062 _142064)) = (@all (cart _142062 _142064)).
Proof. exact (eq_refl (@all (cart _142062 _142064))). Qed.
Lemma lem8009766 {_142062 _142063 _142064 : Type'} (s' : type24 _142062 _142063) (x : cart _142062 _142063) (s : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term134 _142062 _142063 _142064 s t x s' t') = (term501 _142062 _142063 _142064 s' x s t t').
Proof. exact (MK_COMB (@lem8009765 _142062 _142064) (@lem8009764 _142062 _142063 _142064 s' x s t t')). Qed.
Lemma lem8009767 {_142062 _142063 _142064 : Type'} (s' : type24 _142062 _142063) (s : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term142 _142062 _142063 _142064 s t s' t') = (term502 _142062 _142063 _142064 s' s t t').
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8009766 _142062 _142063 _142064 s' x s t t')). Qed.
Lemma lem8009768 {_142062 _142063 : Type'} : (@all (cart _142062 _142063)) = (@all (cart _142062 _142063)).
Proof. exact (eq_refl (@all (cart _142062 _142063))). Qed.
Lemma lem8009770 {_142062 _142063 _142064 : Type'} (s' : type24 _142062 _142063) (s : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term143 _142062 _142063 _142064 s t s' t') = (term503 _142062 _142063 _142064 s' s t t').
Proof. exact (MK_COMB (@lem8009768 _142062 _142063) (@lem8009767 _142062 _142063 _142064 s' s t t')). Qed.
Lemma lem8009771 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : term503 _142062 _142063 _142064 s' s t t'.
Proof. exact (EQ_MP (@lem8009770 _142062 _142063 _142064 s' s t t') (@lem8009661 _142062 _142063 _142064 x y s x' s' t x'' t' h1)). Qed.
Lemma lem8009801 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) : (term71 _142062 _142063 x s) = (term71 _142062 _142063 x s).
Proof. exact (eq_refl (term71 _142062 _142063 x s)). Qed.
Lemma lem8009802 {_142062 _142063 : Type'} (s : type24 _142062 _142063) : (term73 _142062 _142063 s) = (term73 _142062 _142063 s).
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8009801 _142062 _142063 x s)). Qed.
Lemma lem8009803 {_142062 _142063 : Type'} : (@all (cart _142062 _142063)) = (@all (cart _142062 _142063)).
Proof. exact (eq_refl (@all (cart _142062 _142063))). Qed.
Lemma lem8009805 {_142062 _142063 : Type'} (s : type24 _142062 _142063) : (term74 _142062 _142063 s) = (term74 _142062 _142063 s).
Proof. exact (MK_COMB (@lem8009803 _142062 _142063) (@lem8009802 _142062 _142063 s)). Qed.
Lemma lem8009806 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (h1 : term74 _142062 _142063 s) : term74 _142062 _142063 s.
Proof. exact (EQ_MP (@lem8009805 _142062 _142063 s) (@lem8009680 _142062 _142063 s h1)). Qed.
Lemma lem8009820 {_142062 _142064 : Type'} (x : cart _142062 _142064) (t : type24 _142062 _142064) : (term71 _142062 _142064 x t) = (term71 _142062 _142064 x t).
Proof. exact (eq_refl (term71 _142062 _142064 x t)). Qed.
Lemma lem8009821 {_142062 _142064 : Type'} (t : type24 _142062 _142064) : (term73 _142062 _142064 t) = (term73 _142062 _142064 t).
Proof. exact (fun_ext (fun x : cart _142062 _142064 => @lem8009820 _142062 _142064 x t)). Qed.
Lemma lem8009822 {_142062 _142064 : Type'} : (@all (cart _142062 _142064)) = (@all (cart _142062 _142064)).
Proof. exact (eq_refl (@all (cart _142062 _142064))). Qed.
Lemma lem8009824 {_142062 _142064 : Type'} (t : type24 _142062 _142064) : (term74 _142062 _142064 t) = (term74 _142062 _142064 t).
Proof. exact (MK_COMB (@lem8009822 _142062 _142064) (@lem8009821 _142062 _142064 t)). Qed.
Lemma lem8009825 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (h1 : term74 _142062 _142064 t) : term74 _142062 _142064 t.
Proof. exact (EQ_MP (@lem8009824 _142062 _142064 t) (@lem8009682 _142062 _142064 t h1)). Qed.
Lemma lem8009837 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s' : type24 _142062 _142063) (h1 : term71 _142062 _142063 x s') : term71 _142062 _142063 x s'.
Proof. exact (h1). Qed.
Lemma lem8009845 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (x : cart _142062 _142063) (s' : type24 _142062 _142063) : (term154 _142062 _142063 s x s') = (term154 _142062 _142063 s x s').
Proof. exact (eq_refl (term154 _142062 _142063 s x s')). Qed.
Lemma lem8009846 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) : (term162 _142062 _142063 s s') = (term162 _142062 _142063 s s').
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8009845 _142062 _142063 s x s')). Qed.
Lemma lem8009847 {_142062 _142063 : Type'} : (@all (cart _142062 _142063)) = (@all (cart _142062 _142063)).
Proof. exact (eq_refl (@all (cart _142062 _142063))). Qed.
Lemma lem8009849 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) : (term163 _142062 _142063 s s') = (term163 _142062 _142063 s s').
Proof. exact (MK_COMB (@lem8009847 _142062 _142063) (@lem8009846 _142062 _142063 s s')). Qed.
Lemma lem8009850 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term170 _142062 _142063 _142064 s s' t t') : term163 _142062 _142063 s s'.
Proof. exact (EQ_MP (@lem8009849 _142062 _142063 s s') (@lem8009685 _142062 _142063 _142064 s s' t t' h1)). Qed.
Lemma lem8009877 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) : (term71 _142062 _142063 x s) = (term71 _142062 _142063 x s).
Proof. exact (eq_refl (term71 _142062 _142063 x s)). Qed.
Lemma lem8009878 {_142062 _142063 : Type'} (s : type24 _142062 _142063) : (term73 _142062 _142063 s) = (term73 _142062 _142063 s).
Proof. exact (fun_ext (fun x : cart _142062 _142063 => @lem8009877 _142062 _142063 x s)). Qed.
Lemma lem8009879 {_142062 _142063 : Type'} : (@all (cart _142062 _142063)) = (@all (cart _142062 _142063)).
Proof. exact (eq_refl (@all (cart _142062 _142063))). Qed.
Lemma lem8009881 {_142062 _142063 : Type'} (s : type24 _142062 _142063) : (term74 _142062 _142063 s) = (term74 _142062 _142063 s).
Proof. exact (MK_COMB (@lem8009879 _142062 _142063) (@lem8009878 _142062 _142063 s)). Qed.
Lemma lem8009882 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (h1 : term74 _142062 _142063 s) : term74 _142062 _142063 s.
Proof. exact (EQ_MP (@lem8009881 _142062 _142063 s) (@lem8009686 _142062 _142063 s h1)). Qed.
Lemma lem8009896 {_142062 _142064 : Type'} (x : cart _142062 _142064) (t : type24 _142062 _142064) : (term71 _142062 _142064 x t) = (term71 _142062 _142064 x t).
Proof. exact (eq_refl (term71 _142062 _142064 x t)). Qed.
Lemma lem8009897 {_142062 _142064 : Type'} (t : type24 _142062 _142064) : (term73 _142062 _142064 t) = (term73 _142062 _142064 t).
Proof. exact (fun_ext (fun x : cart _142062 _142064 => @lem8009896 _142062 _142064 x t)). Qed.
Lemma lem8009898 {_142062 _142064 : Type'} : (@all (cart _142062 _142064)) = (@all (cart _142062 _142064)).
Proof. exact (eq_refl (@all (cart _142062 _142064))). Qed.
Lemma lem8009900 {_142062 _142064 : Type'} (t : type24 _142062 _142064) : (term74 _142062 _142064 t) = (term74 _142062 _142064 t).
Proof. exact (MK_COMB (@lem8009898 _142062 _142064) (@lem8009897 _142062 _142064 t)). Qed.
Lemma lem8009901 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (h1 : term74 _142062 _142064 t) : term74 _142062 _142064 t.
Proof. exact (EQ_MP (@lem8009900 _142062 _142064 t) (@lem8009688 _142062 _142064 t h1)). Qed.
Lemma lem8009913 {_142062 _142064 : Type'} (y : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term71 _142062 _142064 y t') : term71 _142062 _142064 y t'.
Proof. exact (h1). Qed.
Lemma lem8009934 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (x : cart _142062 _142064) (t' : type24 _142062 _142064) : (term154 _142062 _142064 t x t') = (term154 _142062 _142064 t x t').
Proof. exact (eq_refl (term154 _142062 _142064 t x t')). Qed.
Lemma lem8009935 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term162 _142062 _142064 t t') = (term162 _142062 _142064 t t').
Proof. exact (fun_ext (fun x : cart _142062 _142064 => @lem8009934 _142062 _142064 t x t')). Qed.
Lemma lem8009936 {_142062 _142064 : Type'} : (@all (cart _142062 _142064)) = (@all (cart _142062 _142064)).
Proof. exact (eq_refl (@all (cart _142062 _142064))). Qed.
Lemma lem8009938 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term163 _142062 _142064 t t') = (term163 _142062 _142064 t t').
Proof. exact (MK_COMB (@lem8009936 _142062 _142064) (@lem8009935 _142062 _142064 t t')). Qed.
Lemma lem8009939 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term170 _142062 _142063 _142064 s s' t t') : term163 _142062 _142064 t t'.
Proof. exact (EQ_MP (@lem8009938 _142062 _142064 t t') (@lem8009690 _142062 _142063 _142064 s s' t t' h1)). Qed.
Lemma lem8009940 {_142062 _142063 _142064 : Type'} (_105664 : cart _142062 _142063) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : term504 _142062 _142063 _142064 s' s t t' _105664.
Proof. exact (@lem8009723 _142062 _142063 _142064 x y s x' s' t x'' t' h1 _105664). Qed.
Lemma lem8009941 {_142062 _142063 _142064 : Type'} (s' : type24 _142062 _142063) (_105664 : cart _142062 _142063) (s : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term504 _142062 _142063 _142064 s' s t t' _105664) = (term501 _142062 _142063 _142064 s' _105664 s t t').
Proof. exact (eq_refl (term504 _142062 _142063 _142064 s' s t t' _105664)). Qed.
Lemma lem8009942 {_142062 _142063 _142064 : Type'} (_105664 : cart _142062 _142063) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : term501 _142062 _142063 _142064 s' _105664 s t t'.
Proof. exact (EQ_MP (@lem8009941 _142062 _142063 _142064 s' _105664 s t t') (@lem8009940 _142062 _142063 _142064 _105664 x y s x' s' t x'' t' h1)). Qed.
Lemma lem8009943 {_142062 _142063 _142064 : Type'} (_105664 : cart _142062 _142063) (_105665 : cart _142062 _142064) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : term505 _142062 _142063 _142064 s' _105664 s t t' _105665.
Proof. exact (@lem8009942 _142062 _142063 _142064 _105664 x y s x' s' t x'' t' h1 _105665). Qed.
Lemma lem8009944 {_142062 _142063 _142064 : Type'} (s' : type24 _142062 _142063) (_105664 : cart _142062 _142063) (s : type24 _142062 _142063) (t : type24 _142062 _142064) (_105665 : cart _142062 _142064) (t' : type24 _142062 _142064) : (term505 _142062 _142063 _142064 s' _105664 s t t' _105665) = (term499 _142062 _142063 _142064 s' _105664 s t _105665 t').
Proof. exact (eq_refl (term505 _142062 _142063 _142064 s' _105664 s t t' _105665)). Qed.
Lemma lem8009945 {_142062 _142063 _142064 : Type'} (_105664 : cart _142062 _142063) (_105665 : cart _142062 _142064) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : term499 _142062 _142063 _142064 s' _105664 s t _105665 t'.
Proof. exact (EQ_MP (@lem8009944 _142062 _142063 _142064 s' _105664 s t _105665 t') (@lem8009943 _142062 _142063 _142064 _105664 _105665 x y s x' s' t x'' t' h1)). Qed.
Lemma lem8009946 {_142062 _142063 _142064 : Type'} (_105666 : cart _142062 _142063) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : term504 _142062 _142063 _142064 s' s t t' _105666.
Proof. exact (@lem8009771 _142062 _142063 _142064 x y s x' s' t x'' t' h1 _105666). Qed.
Lemma lem8009947 {_142062 _142063 _142064 : Type'} (s' : type24 _142062 _142063) (_105666 : cart _142062 _142063) (s : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term504 _142062 _142063 _142064 s' s t t' _105666) = (term501 _142062 _142063 _142064 s' _105666 s t t').
Proof. exact (eq_refl (term504 _142062 _142063 _142064 s' s t t' _105666)). Qed.
Lemma lem8009948 {_142062 _142063 _142064 : Type'} (_105666 : cart _142062 _142063) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : term501 _142062 _142063 _142064 s' _105666 s t t'.
Proof. exact (EQ_MP (@lem8009947 _142062 _142063 _142064 s' _105666 s t t') (@lem8009946 _142062 _142063 _142064 _105666 x y s x' s' t x'' t' h1)). Qed.
Lemma lem8009949 {_142062 _142063 _142064 : Type'} (_105666 : cart _142062 _142063) (_105667 : cart _142062 _142064) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : term505 _142062 _142063 _142064 s' _105666 s t t' _105667.
Proof. exact (@lem8009948 _142062 _142063 _142064 _105666 x y s x' s' t x'' t' h1 _105667). Qed.
Lemma lem8009950 {_142062 _142063 _142064 : Type'} (s' : type24 _142062 _142063) (_105666 : cart _142062 _142063) (s : type24 _142062 _142063) (t : type24 _142062 _142064) (_105667 : cart _142062 _142064) (t' : type24 _142062 _142064) : (term505 _142062 _142063 _142064 s' _105666 s t t' _105667) = (term499 _142062 _142063 _142064 s' _105666 s t _105667 t').
Proof. exact (eq_refl (term505 _142062 _142063 _142064 s' _105666 s t t' _105667)). Qed.
Lemma lem8009951 {_142062 _142063 _142064 : Type'} (_105666 : cart _142062 _142063) (_105667 : cart _142062 _142064) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : term499 _142062 _142063 _142064 s' _105666 s t _105667 t'.
Proof. exact (EQ_MP (@lem8009950 _142062 _142063 _142064 s' _105666 s t _105667 t') (@lem8009949 _142062 _142063 _142064 _105666 _105667 x y s x' s' t x'' t' h1)). Qed.
Lemma lem8009952 {_142062 _142063 : Type'} (_105668 : cart _142062 _142063) (s : type24 _142062 _142063) (h1 : term74 _142062 _142063 s) : term147 _142062 _142063 s _105668.
Proof. exact (@lem8009806 _142062 _142063 s h1 _105668). Qed.
Lemma lem8009953 {_142062 _142063 : Type'} (_105668 : cart _142062 _142063) (s : type24 _142062 _142063) : (term147 _142062 _142063 s _105668) = (term71 _142062 _142063 _105668 s).
Proof. exact (eq_refl (term147 _142062 _142063 s _105668)). Qed.
Lemma lem8009955 {_142062 _142064 : Type'} (_105669 : cart _142062 _142064) (t : type24 _142062 _142064) (h1 : term74 _142062 _142064 t) : term147 _142062 _142064 t _105669.
Proof. exact (@lem8009825 _142062 _142064 t h1 _105669). Qed.
Lemma lem8009956 {_142062 _142064 : Type'} (_105669 : cart _142062 _142064) (t : type24 _142062 _142064) : (term147 _142062 _142064 t _105669) = (term71 _142062 _142064 _105669 t).
Proof. exact (eq_refl (term147 _142062 _142064 t _105669)). Qed.
Lemma lem8009958 {_142062 _142063 _142064 : Type'} (_105670 : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term170 _142062 _142063 _142064 s s' t t') : term506 _142062 _142063 s s' _105670.
Proof. exact (@lem8009850 _142062 _142063 _142064 s s' t t' h1 _105670). Qed.
Lemma lem8009959 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (_105670 : cart _142062 _142063) (s' : type24 _142062 _142063) : (term506 _142062 _142063 s s' _105670) = (term154 _142062 _142063 s _105670 s').
Proof. exact (eq_refl (term506 _142062 _142063 s s' _105670)). Qed.
Lemma lem8009964 {_142062 _142063 : Type'} (_105672 : cart _142062 _142063) (s : type24 _142062 _142063) (h1 : term74 _142062 _142063 s) : term147 _142062 _142063 s _105672.
Proof. exact (@lem8009882 _142062 _142063 s h1 _105672). Qed.
Lemma lem8009965 {_142062 _142063 : Type'} (_105672 : cart _142062 _142063) (s : type24 _142062 _142063) : (term147 _142062 _142063 s _105672) = (term71 _142062 _142063 _105672 s).
Proof. exact (eq_refl (term147 _142062 _142063 s _105672)). Qed.
Lemma lem8009967 {_142062 _142064 : Type'} (_105673 : cart _142062 _142064) (t : type24 _142062 _142064) (h1 : term74 _142062 _142064 t) : term147 _142062 _142064 t _105673.
Proof. exact (@lem8009901 _142062 _142064 t h1 _105673). Qed.
Lemma lem8009968 {_142062 _142064 : Type'} (_105673 : cart _142062 _142064) (t : type24 _142062 _142064) : (term147 _142062 _142064 t _105673) = (term71 _142062 _142064 _105673 t).
Proof. exact (eq_refl (term147 _142062 _142064 t _105673)). Qed.
Lemma lem8009973 {_142062 _142063 _142064 : Type'} (_105675 : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term170 _142062 _142063 _142064 s s' t t') : term506 _142062 _142064 t t' _105675.
Proof. exact (@lem8009939 _142062 _142063 _142064 s s' t t' h1 _105675). Qed.
Lemma lem8009974 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (_105675 : cart _142062 _142064) (t' : type24 _142062 _142064) : (term506 _142062 _142064 t t' _105675) = (term154 _142062 _142064 t _105675 t').
Proof. exact (eq_refl (term506 _142062 _142064 t t' _105675)). Qed.
Lemma lem8009977 {_142062 _142063 _142064 : Type'} (_105665 : cart _142062 _142064) (_105664 : cart _142062 _142063) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : term507 _142062 _142063 _142064 s _105665 t _105664 s'.
Proof. exact (proj1 (@lem8009945 _142062 _142063 _142064 _105664 _105665 x y s x' s' t x'' t' h1)). Qed.
Lemma lem8009978 {_142062 _142063 _142064 : Type'} (_105666 : cart _142062 _142063) (_105667 : cart _142062 _142064) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : term508 _142062 _142063 _142064 _105666 s t _105667 t'.
Proof. exact (proj2 (@lem8009951 _142062 _142063 _142064 _105666 _105667 x y s x' s' t x'' t' h1)). Qed.
Lemma lem8009987 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (h1 : term153 _142062 _142063 s x' s') : term71 _142062 _142063 x' s'.
Proof. exact (proj2 (@lem8009666 _142062 _142063 s x' s' h1)). Qed.
Lemma lem8009998 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (_105665 : cart _142062 _142064) (t : type24 _142062 _142064) (_105664 : cart _142062 _142063) (s' : type24 _142062 _142063) : (term507 _142062 _142063 _142064 s _105665 t _105664 s') = (term509 _142062 _142063 _142064 s _105665 t _105664 s').
Proof. exact (@lem8006159 (term71 _142062 _142063 _105664 s) (term71 _142062 _142064 _105665 t) (@IN (cart _142062 _142063) _105664 s')). Qed.
Lemma lem8009999 {_142062 _142063 _142064 : Type'} (_105665 : cart _142062 _142064) (_105664 : cart _142062 _142063) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : term509 _142062 _142063 _142064 s _105665 t _105664 s'.
Proof. exact (EQ_MP (@lem8009998 _142062 _142063 _142064 s _105665 t _105664 s') (@lem8009977 _142062 _142063 _142064 _105665 _105664 x y s x' s' t x'' t' h1)). Qed.
Lemma lem8010019 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term153 _142062 _142064 t x'' t') : term71 _142062 _142064 x'' t'.
Proof. exact (proj2 (@lem8009667 _142062 _142064 t x'' t' h1)). Qed.
Lemma lem8010042 {_142062 _142063 _142064 : Type'} (_105666 : cart _142062 _142063) (s : type24 _142062 _142063) (t : type24 _142062 _142064) (_105667 : cart _142062 _142064) (t' : type24 _142062 _142064) : (term508 _142062 _142063 _142064 _105666 s t _105667 t') = (term510 _142062 _142063 _142064 _105666 s t _105667 t').
Proof. exact (@lem8006159 (term71 _142062 _142063 _105666 s) (term71 _142062 _142064 _105667 t) (@IN (cart _142062 _142064) _105667 t')). Qed.
Lemma lem8010043 {_142062 _142063 _142064 : Type'} (_105666 : cart _142062 _142063) (_105667 : cart _142062 _142064) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : term510 _142062 _142063 _142064 _105666 s t _105667 t'.
Proof. exact (EQ_MP (@lem8010042 _142062 _142063 _142064 _105666 s t _105667 t') (@lem8009978 _142062 _142063 _142064 _105666 _105667 x y s x' s' t x'' t' h1)). Qed.
Lemma lem8010051 {_142062 _142063 : Type'} (_105668 : cart _142062 _142063) (s : type24 _142062 _142063) (h1 : term74 _142062 _142063 s) : term71 _142062 _142063 _105668 s.
Proof. exact (EQ_MP (@lem8009953 _142062 _142063 _105668 s) (@lem8009952 _142062 _142063 _105668 s h1)). Qed.
Lemma lem8010059 {_142062 _142064 : Type'} (_105669 : cart _142062 _142064) (t : type24 _142062 _142064) (h1 : term74 _142062 _142064 t) : term71 _142062 _142064 _105669 t.
Proof. exact (EQ_MP (@lem8009956 _142062 _142064 _105669 t) (@lem8009955 _142062 _142064 _105669 t h1)). Qed.
Lemma lem8010065 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s' : type24 _142062 _142063) (h1 : term71 _142062 _142063 x s') : term71 _142062 _142063 x s'.
Proof. exact (h1). Qed.
Lemma lem8010071 {_142062 _142063 _142064 : Type'} (_105670 : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term170 _142062 _142063 _142064 s s' t t') : term154 _142062 _142063 s _105670 s'.
Proof. exact (EQ_MP (@lem8009959 _142062 _142063 s _105670 s') (@lem8009958 _142062 _142063 _142064 _105670 s s' t t' h1)). Qed.
Lemma lem8010085 {_142062 _142063 : Type'} (_105672 : cart _142062 _142063) (s : type24 _142062 _142063) (h1 : term74 _142062 _142063 s) : term71 _142062 _142063 _105672 s.
Proof. exact (EQ_MP (@lem8009965 _142062 _142063 _105672 s) (@lem8009964 _142062 _142063 _105672 s h1)). Qed.
Lemma lem8010093 {_142062 _142064 : Type'} (_105673 : cart _142062 _142064) (t : type24 _142062 _142064) (h1 : term74 _142062 _142064 t) : term71 _142062 _142064 _105673 t.
Proof. exact (EQ_MP (@lem8009968 _142062 _142064 _105673 t) (@lem8009967 _142062 _142064 _105673 t h1)). Qed.
Lemma lem8010099 {_142062 _142064 : Type'} (y : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term71 _142062 _142064 y t') : term71 _142062 _142064 y t'.
Proof. exact (h1). Qed.
Lemma lem8010111 {_142062 _142063 _142064 : Type'} (_105675 : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term170 _142062 _142063 _142064 s s' t t') : term154 _142062 _142064 t _105675 t'.
Proof. exact (EQ_MP (@lem8009974 _142062 _142064 t _105675 t') (@lem8009973 _142062 _142063 _142064 _105675 s s' t t' h1)). Qed.
Lemma lem8010113 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (h1 : term153 _142062 _142063 s x' s') : @IN (cart _142062 _142063) x' s.
Proof. exact (proj1 (@lem8009666 _142062 _142063 s x' s' h1)). Qed.
Lemma lem8010114 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (h1 : term153 _142062 _142063 s x' s') : term511 _142062 _142063 x' s.
Proof. exact (fun h0 : term71 _142062 _142063 x' s => @lem8010113 _142062 _142063 s x' s' h1). Qed.
Lemma lem8010116 (p : Prop) : (term512 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8010117 {_142062 _142063 : Type'} (x' : cart _142062 _142063) (s : type24 _142062 _142063) : (term511 _142062 _142063 x' s) = (@IN (cart _142062 _142063) x' s).
Proof. exact (@lem8010116 (@IN (cart _142062 _142063) x' s)). Qed.
Lemma lem8010118 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (h1 : term153 _142062 _142063 s x' s') : @IN (cart _142062 _142063) x' s.
Proof. exact (EQ_MP (@lem8010117 _142062 _142063 x' s) (@lem8010114 _142062 _142063 s x' s' h1)). Qed.
Lemma lem8010120 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : @IN (cart _142062 _142064) y t.
Proof. exact (proj1 (@lem8009662 _142062 _142063 _142064 x y s x' s' t x'' t' h1)). Qed.
Lemma lem8010121 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : term511 _142062 _142064 y t.
Proof. exact (fun h0 : term71 _142062 _142064 y t => @lem8010120 _142062 _142063 _142064 x y s x' s' t x'' t' h1). Qed.
Lemma lem8010123 (p : Prop) : (term512 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8010124 {_142062 _142064 : Type'} (y : cart _142062 _142064) (t : type24 _142062 _142064) : (term511 _142062 _142064 y t) = (@IN (cart _142062 _142064) y t).
Proof. exact (@lem8010123 (@IN (cart _142062 _142064) y t)). Qed.
Lemma lem8010125 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : @IN (cart _142062 _142064) y t.
Proof. exact (EQ_MP (@lem8010124 _142062 _142064 y t) (@lem8010121 _142062 _142063 _142064 x y s x' s' t x'' t' h1)). Qed.
Lemma lem8010141 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8010142 {_142062 _142063 _142064 : Type'} (_105664 : cart _142062 _142063) (s' : type24 _142062 _142063) (_105665 : cart _142062 _142064) (t : type24 _142062 _142064) : (term513 _142062 _142063 _142064 _105665 t _105664 s') = (term514 _142062 _142063 _142064 _105664 s' _105665 t).
Proof. exact (@lem8010141 (@IN (cart _142062 _142063) _105664 s') (term71 _142062 _142064 _105665 t)). Qed.
Lemma lem8010148 {_142062 _142063 : Type'} (_105664 : cart _142062 _142063) (s : type24 _142062 _142063) : (term515 _142062 _142063 _105664 s) = (term515 _142062 _142063 _105664 s).
Proof. exact (eq_refl (term515 _142062 _142063 _105664 s)). Qed.
Lemma lem8010149 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (_105664 : cart _142062 _142063) (s' : type24 _142062 _142063) (_105665 : cart _142062 _142064) (t : type24 _142062 _142064) : (term509 _142062 _142063 _142064 s _105665 t _105664 s') = (term516 _142062 _142063 _142064 s _105664 s' _105665 t).
Proof. exact (MK_COMB (@lem8010148 _142062 _142063 _105664 s) (@lem8010142 _142062 _142063 _142064 _105664 s' _105665 t)). Qed.
Lemma lem8010153 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8010154 {_142062 _142063 _142064 : Type'} (s' : type24 _142062 _142063) (_105664 : cart _142062 _142063) (s : type24 _142062 _142063) (_105665 : cart _142062 _142064) (t : type24 _142062 _142064) : (term516 _142062 _142063 _142064 s _105664 s' _105665 t) = (term517 _142062 _142063 _142064 s' _105664 s _105665 t).
Proof. exact (@lem8010153 (@IN (cart _142062 _142063) _105664 s') (term71 _142062 _142063 _105664 s) (term71 _142062 _142064 _105665 t)). Qed.
Lemma lem8010170 {_142062 _142063 _142064 : Type'} (s' : type24 _142062 _142063) (_105664 : cart _142062 _142063) (s : type24 _142062 _142063) (_105665 : cart _142062 _142064) (t : type24 _142062 _142064) : (term509 _142062 _142063 _142064 s _105665 t _105664 s') = (term517 _142062 _142063 _142064 s' _105664 s _105665 t).
Proof. exact (TRANS (@lem8010149 _142062 _142063 _142064 s _105664 s' _105665 t) (@lem8010154 _142062 _142063 _142064 s' _105664 s _105665 t)). Qed.
Lemma lem8010171 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8010172 {_142062 _142063 _142064 : Type'} (s' : type24 _142062 _142063) (_105664 : cart _142062 _142063) (s : type24 _142062 _142063) (_105665 : cart _142062 _142064) (t : type24 _142062 _142064) : (term518 _142062 _142063 _142064 s _105665 t _105664 s') = (term519 _142062 _142063 _142064 s' _105664 s _105665 t).
Proof. exact (MK_COMB (@lem8010171) (@lem8010170 _142062 _142063 _142064 s' _105664 s _105665 t)). Qed.
Lemma lem8010188 {_142062 _142063 _142064 : Type'} (s' : type24 _142062 _142063) (_105664 : cart _142062 _142063) (s : type24 _142062 _142063) (_105665 : cart _142062 _142064) (t : type24 _142062 _142064) : (term517 _142062 _142063 _142064 s' _105664 s _105665 t) = (term517 _142062 _142063 _142064 s' _105664 s _105665 t).
Proof. exact (eq_refl (term517 _142062 _142063 _142064 s' _105664 s _105665 t)). Qed.
Lemma lem8010189 {_142062 _142063 _142064 : Type'} (s' : type24 _142062 _142063) (_105664 : cart _142062 _142063) (s : type24 _142062 _142063) (_105665 : cart _142062 _142064) (t : type24 _142062 _142064) : ((term509 _142062 _142063 _142064 s _105665 t _105664 s') = (term517 _142062 _142063 _142064 s' _105664 s _105665 t)) = ((term517 _142062 _142063 _142064 s' _105664 s _105665 t) = (term517 _142062 _142063 _142064 s' _105664 s _105665 t)).
Proof. exact (MK_COMB (@lem8010172 _142062 _142063 _142064 s' _105664 s _105665 t) (@lem8010188 _142062 _142063 _142064 s' _105664 s _105665 t)). Qed.
Lemma lem8010191 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8010192 (x : Prop) : (x = x) = True.
Proof. exact (@lem8010191 Prop x). Qed.
Lemma lem8010193 {_142062 _142063 _142064 : Type'} (s' : type24 _142062 _142063) (_105664 : cart _142062 _142063) (s : type24 _142062 _142063) (_105665 : cart _142062 _142064) (t : type24 _142062 _142064) : ((term517 _142062 _142063 _142064 s' _105664 s _105665 t) = (term517 _142062 _142063 _142064 s' _105664 s _105665 t)) = True.
Proof. exact (@lem8010192 (term517 _142062 _142063 _142064 s' _105664 s _105665 t)). Qed.
Lemma lem8010194 {_142062 _142063 _142064 : Type'} (s' : type24 _142062 _142063) (_105664 : cart _142062 _142063) (s : type24 _142062 _142063) (_105665 : cart _142062 _142064) (t : type24 _142062 _142064) : ((term509 _142062 _142063 _142064 s _105665 t _105664 s') = (term517 _142062 _142063 _142064 s' _105664 s _105665 t)) = True.
Proof. exact (TRANS (@lem8010189 _142062 _142063 _142064 s' _105664 s _105665 t) (@lem8010193 _142062 _142063 _142064 s' _105664 s _105665 t)). Qed.
Lemma lem8010195 {_142062 _142063 _142064 : Type'} (s' : type24 _142062 _142063) (_105664 : cart _142062 _142063) (s : type24 _142062 _142063) (_105665 : cart _142062 _142064) (t : type24 _142062 _142064) : True = ((term509 _142062 _142063 _142064 s _105665 t _105664 s') = (term517 _142062 _142063 _142064 s' _105664 s _105665 t)).
Proof. exact (SYM (@lem8010194 _142062 _142063 _142064 s' _105664 s _105665 t)). Qed.
Lemma lem8010196 {_142062 _142063 _142064 : Type'} (s' : type24 _142062 _142063) (_105664 : cart _142062 _142063) (s : type24 _142062 _142063) (_105665 : cart _142062 _142064) (t : type24 _142062 _142064) : (term509 _142062 _142063 _142064 s _105665 t _105664 s') = (term517 _142062 _142063 _142064 s' _105664 s _105665 t).
Proof. exact (EQ_MP (@lem8010195 _142062 _142063 _142064 s' _105664 s _105665 t) (@lem0)). Qed.
Lemma lem8010197 {_142062 _142063 _142064 : Type'} (_105664 : cart _142062 _142063) (_105665 : cart _142062 _142064) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : term517 _142062 _142063 _142064 s' _105664 s _105665 t.
Proof. exact (EQ_MP (@lem8010196 _142062 _142063 _142064 s' _105664 s _105665 t) (@lem8009999 _142062 _142063 _142064 _105665 _105664 x y s x' s' t x'' t' h1)). Qed.
Lemma lem8010199 (b : Prop) (a : Prop) : (a \/ b) = (term520 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8010200 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (_105665 : cart _142062 _142064) (t : type24 _142062 _142064) (_105664 : cart _142062 _142063) (s' : type24 _142062 _142063) : (term517 _142062 _142063 _142064 s' _105664 s _105665 t) = (term521 _142062 _142063 _142064 s _105665 t _105664 s').
Proof. exact (@lem8010199 (term115 _142062 _142063 _142064 _105664 s _105665 t) (@IN (cart _142062 _142063) _105664 s')). Qed.
Lemma lem8010202 (a : Prop) (b : Prop) : (term522 a b) = (term523 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8010203 {_142062 _142063 _142064 : Type'} (_105664 : cart _142062 _142063) (s : type24 _142062 _142063) (_105665 : cart _142062 _142064) (t : type24 _142062 _142064) : (term524 _142062 _142063 _142064 _105664 s _105665 t) = (term525 _142062 _142063 _142064 _105664 s _105665 t).
Proof. exact (@lem8010202 (term71 _142062 _142063 _105664 s) (term71 _142062 _142064 _105665 t)). Qed.
Lemma lem8010205 (a : Prop) : (term109 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8010206 {_142062 _142063 : Type'} (_105664 : cart _142062 _142063) (s : type24 _142062 _142063) : (term144 _142062 _142063 _105664 s) = (@IN (cart _142062 _142063) _105664 s).
Proof. exact (@lem8010205 (@IN (cart _142062 _142063) _105664 s)). Qed.
Lemma lem8010207 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8010208 {_142062 _142063 : Type'} (_105664 : cart _142062 _142063) (s : type24 _142062 _142063) : (term526 _142062 _142063 _105664 s) = (term241 _142062 _142063 _105664 s).
Proof. exact (MK_COMB (@lem8010207) (@lem8010206 _142062 _142063 _105664 s)). Qed.
Lemma lem8010210 (a : Prop) : (term109 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8010211 {_142062 _142064 : Type'} (_105665 : cart _142062 _142064) (t : type24 _142062 _142064) : (term144 _142062 _142064 _105665 t) = (@IN (cart _142062 _142064) _105665 t).
Proof. exact (@lem8010210 (@IN (cart _142062 _142064) _105665 t)). Qed.
Lemma lem8010212 {_142062 _142063 _142064 : Type'} (_105664 : cart _142062 _142063) (s : type24 _142062 _142063) (_105665 : cart _142062 _142064) (t : type24 _142062 _142064) : (term525 _142062 _142063 _142064 _105664 s _105665 t) = (term18 _142062 _142063 _142064 _105664 s _105665 t).
Proof. exact (MK_COMB (@lem8010208 _142062 _142063 _105664 s) (@lem8010211 _142062 _142064 _105665 t)). Qed.
Lemma lem8010213 {_142062 _142063 _142064 : Type'} (_105664 : cart _142062 _142063) (s : type24 _142062 _142063) (_105665 : cart _142062 _142064) (t : type24 _142062 _142064) : (term524 _142062 _142063 _142064 _105664 s _105665 t) = (term18 _142062 _142063 _142064 _105664 s _105665 t).
Proof. exact (TRANS (@lem8010203 _142062 _142063 _142064 _105664 s _105665 t) (@lem8010212 _142062 _142063 _142064 _105664 s _105665 t)). Qed.
Lemma lem8010214 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8010215 {_142062 _142063 _142064 : Type'} (_105664 : cart _142062 _142063) (s : type24 _142062 _142063) (_105665 : cart _142062 _142064) (t : type24 _142062 _142064) : (term527 _142062 _142063 _142064 _105664 s _105665 t) = (term528 _142062 _142063 _142064 _105664 s _105665 t).
Proof. exact (MK_COMB (@lem8010214) (@lem8010213 _142062 _142063 _142064 _105664 s _105665 t)). Qed.
Lemma lem8010216 {_142062 _142063 : Type'} (_105664 : cart _142062 _142063) (s' : type24 _142062 _142063) : (@IN (cart _142062 _142063) _105664 s') = (@IN (cart _142062 _142063) _105664 s').
Proof. exact (eq_refl (@IN (cart _142062 _142063) _105664 s')). Qed.
Lemma lem8010217 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (_105665 : cart _142062 _142064) (t : type24 _142062 _142064) (_105664 : cart _142062 _142063) (s' : type24 _142062 _142063) : (term521 _142062 _142063 _142064 s _105665 t _105664 s') = (term529 _142062 _142063 _142064 s _105665 t _105664 s').
Proof. exact (MK_COMB (@lem8010215 _142062 _142063 _142064 _105664 s _105665 t) (@lem8010216 _142062 _142063 _105664 s')). Qed.
Lemma lem8010218 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (_105665 : cart _142062 _142064) (t : type24 _142062 _142064) (_105664 : cart _142062 _142063) (s' : type24 _142062 _142063) : (term517 _142062 _142063 _142064 s' _105664 s _105665 t) = (term529 _142062 _142063 _142064 s _105665 t _105664 s').
Proof. exact (TRANS (@lem8010200 _142062 _142063 _142064 s _105665 t _105664 s') (@lem8010217 _142062 _142063 _142064 s _105665 t _105664 s')). Qed.
Lemma lem8010220 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') (h2 : term153 _142062 _142063 s x' s') : term18 _142062 _142063 _142064 x' s y t.
Proof. exact (conj (@lem8010118 _142062 _142063 s x' s' h2) (@lem8010125 _142062 _142063 _142064 x y s x' s' t x'' t' h1)). Qed.
Lemma lem8010222 {_142062 _142063 _142064 : Type'} (_105665 : cart _142062 _142064) (_105664 : cart _142062 _142063) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : term529 _142062 _142063 _142064 s _105665 t _105664 s'.
Proof. exact (EQ_MP (@lem8010218 _142062 _142063 _142064 s _105665 t _105664 s') (@lem8010197 _142062 _142063 _142064 _105664 _105665 x y s x' s' t x'' t' h1)). Qed.
Lemma lem8010223 {_142062 _142063 _142064 : Type'} (_105665 : cart _142062 _142064) (_105664 : cart _142062 _142063) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : term529 _142062 _142063 _142064 s _105665 t _105664 s'.
Proof. exact (@lem8010222 _142062 _142063 _142064 _105665 _105664 x y s x' s' t x'' t' h1). Qed.
Lemma lem8010224 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : term529 _142062 _142063 _142064 s y t x' s'.
Proof. exact (@lem8010223 _142062 _142063 _142064 y x' x y s x' s' t x'' t' h1). Qed.
Lemma lem8010227 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') (h2 : term153 _142062 _142063 s x' s') : @IN (cart _142062 _142063) x' s'.
Proof. exact (@lem8010224 _142062 _142063 _142064 x y s x' s' t x'' t' h1 (@lem8010220 _142062 _142063 _142064 x y t x'' t' s x' s' h1 h2)). Qed.
Lemma lem8010228 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') (h2 : term153 _142062 _142063 s x' s') : term511 _142062 _142063 x' s'.
Proof. exact (fun h0 : term71 _142062 _142063 x' s' => @lem8010227 _142062 _142063 _142064 x y t x'' t' s x' s' h1 h2). Qed.
Lemma lem8010230 (p : Prop) : (term512 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8010231 {_142062 _142063 : Type'} (x' : cart _142062 _142063) (s' : type24 _142062 _142063) : (term511 _142062 _142063 x' s') = (@IN (cart _142062 _142063) x' s').
Proof. exact (@lem8010230 (@IN (cart _142062 _142063) x' s')). Qed.
Lemma lem8010232 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') (h2 : term153 _142062 _142063 s x' s') : @IN (cart _142062 _142063) x' s'.
Proof. exact (EQ_MP (@lem8010231 _142062 _142063 x' s') (@lem8010228 _142062 _142063 _142064 x y t x'' t' s x' s' h1 h2)). Qed.
Lemma lem8010235 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8010237 {_142062 _142063 : Type'} (x' : cart _142062 _142063) (s' : type24 _142062 _142063) : (term71 _142062 _142063 x' s') = (term530 _142062 _142063 x' s').
Proof. exact (@lem8010235 (@IN (cart _142062 _142063) x' s')). Qed.
Lemma lem8010240 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (h1 : term153 _142062 _142063 s x' s') : term530 _142062 _142063 x' s'.
Proof. exact (EQ_MP (@lem8010237 _142062 _142063 x' s') (@lem8009987 _142062 _142063 s x' s' h1)). Qed.
Lemma lem8010243 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') (h2 : term153 _142062 _142063 s x' s') : False.
Proof. exact (@lem8010240 _142062 _142063 s x' s' h2 (@lem8010232 _142062 _142063 _142064 x y t x'' t' s x' s' h1 h2)). Qed.
Lemma lem8010244 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') (h2 : term153 _142062 _142063 s x' s') : term531.
Proof. exact (fun h0 : ~ False => @lem8010243 _142062 _142063 _142064 x y t x'' t' s x' s' h1 h2). Qed.
Lemma lem8010246 (p : Prop) : (term512 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8010247 : term531 = False.
Proof. exact (@lem8010246 False). Qed.
Lemma lem8010248 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') (h2 : term153 _142062 _142063 s x' s') : False.
Proof. exact (EQ_MP (@lem8010247) (@lem8010244 _142062 _142063 _142064 x y t x'' t' s x' s' h1 h2)). Qed.
Lemma lem8010250 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : @IN (cart _142062 _142063) x s.
Proof. exact (proj1 (@lem8009660 _142062 _142063 _142064 x y s x' s' t x'' t' h1)). Qed.
Lemma lem8010251 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : term511 _142062 _142063 x s.
Proof. exact (fun h0 : term71 _142062 _142063 x s => @lem8010250 _142062 _142063 _142064 x y s x' s' t x'' t' h1). Qed.
Lemma lem8010253 (p : Prop) : (term512 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8010254 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) : (term511 _142062 _142063 x s) = (@IN (cart _142062 _142063) x s).
Proof. exact (@lem8010253 (@IN (cart _142062 _142063) x s)). Qed.
Lemma lem8010255 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : @IN (cart _142062 _142063) x s.
Proof. exact (EQ_MP (@lem8010254 _142062 _142063 x s) (@lem8010251 _142062 _142063 _142064 x y s x' s' t x'' t' h1)). Qed.
Lemma lem8010257 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term153 _142062 _142064 t x'' t') : @IN (cart _142062 _142064) x'' t.
Proof. exact (proj1 (@lem8009667 _142062 _142064 t x'' t' h1)). Qed.
Lemma lem8010258 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term153 _142062 _142064 t x'' t') : term511 _142062 _142064 x'' t.
Proof. exact (fun h0 : term71 _142062 _142064 x'' t => @lem8010257 _142062 _142064 t x'' t' h1). Qed.
Lemma lem8010260 (p : Prop) : (term512 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8010261 {_142062 _142064 : Type'} (x'' : cart _142062 _142064) (t : type24 _142062 _142064) : (term511 _142062 _142064 x'' t) = (@IN (cart _142062 _142064) x'' t).
Proof. exact (@lem8010260 (@IN (cart _142062 _142064) x'' t)). Qed.
Lemma lem8010262 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term153 _142062 _142064 t x'' t') : @IN (cart _142062 _142064) x'' t.
Proof. exact (EQ_MP (@lem8010261 _142062 _142064 x'' t) (@lem8010258 _142062 _142064 t x'' t' h1)). Qed.
Lemma lem8010278 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8010279 {_142062 _142064 : Type'} (t' : type24 _142062 _142064) (_105667 : cart _142062 _142064) (t : type24 _142062 _142064) : (term154 _142062 _142064 t _105667 t') = (term532 _142062 _142064 t' _105667 t).
Proof. exact (@lem8010278 (@IN (cart _142062 _142064) _105667 t') (term71 _142062 _142064 _105667 t)). Qed.
Lemma lem8010285 {_142062 _142063 : Type'} (_105666 : cart _142062 _142063) (s : type24 _142062 _142063) : (term515 _142062 _142063 _105666 s) = (term515 _142062 _142063 _105666 s).
Proof. exact (eq_refl (term515 _142062 _142063 _105666 s)). Qed.
Lemma lem8010286 {_142062 _142063 _142064 : Type'} (_105666 : cart _142062 _142063) (s : type24 _142062 _142063) (t' : type24 _142062 _142064) (_105667 : cart _142062 _142064) (t : type24 _142062 _142064) : (term510 _142062 _142063 _142064 _105666 s t _105667 t') = (term533 _142062 _142063 _142064 _105666 s t' _105667 t).
Proof. exact (MK_COMB (@lem8010285 _142062 _142063 _105666 s) (@lem8010279 _142062 _142064 t' _105667 t)). Qed.
Lemma lem8010290 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8010291 {_142062 _142063 _142064 : Type'} (t' : type24 _142062 _142064) (_105666 : cart _142062 _142063) (s : type24 _142062 _142063) (_105667 : cart _142062 _142064) (t : type24 _142062 _142064) : (term533 _142062 _142063 _142064 _105666 s t' _105667 t) = (term534 _142062 _142063 _142064 t' _105666 s _105667 t).
Proof. exact (@lem8010290 (@IN (cart _142062 _142064) _105667 t') (term71 _142062 _142063 _105666 s) (term71 _142062 _142064 _105667 t)). Qed.
Lemma lem8010307 {_142062 _142063 _142064 : Type'} (t' : type24 _142062 _142064) (_105666 : cart _142062 _142063) (s : type24 _142062 _142063) (_105667 : cart _142062 _142064) (t : type24 _142062 _142064) : (term510 _142062 _142063 _142064 _105666 s t _105667 t') = (term534 _142062 _142063 _142064 t' _105666 s _105667 t).
Proof. exact (TRANS (@lem8010286 _142062 _142063 _142064 _105666 s t' _105667 t) (@lem8010291 _142062 _142063 _142064 t' _105666 s _105667 t)). Qed.
Lemma lem8010308 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8010309 {_142062 _142063 _142064 : Type'} (t' : type24 _142062 _142064) (_105666 : cart _142062 _142063) (s : type24 _142062 _142063) (_105667 : cart _142062 _142064) (t : type24 _142062 _142064) : (term535 _142062 _142063 _142064 _105666 s t _105667 t') = (term536 _142062 _142063 _142064 t' _105666 s _105667 t).
Proof. exact (MK_COMB (@lem8010308) (@lem8010307 _142062 _142063 _142064 t' _105666 s _105667 t)). Qed.
Lemma lem8010325 {_142062 _142063 _142064 : Type'} (t' : type24 _142062 _142064) (_105666 : cart _142062 _142063) (s : type24 _142062 _142063) (_105667 : cart _142062 _142064) (t : type24 _142062 _142064) : (term534 _142062 _142063 _142064 t' _105666 s _105667 t) = (term534 _142062 _142063 _142064 t' _105666 s _105667 t).
Proof. exact (eq_refl (term534 _142062 _142063 _142064 t' _105666 s _105667 t)). Qed.
Lemma lem8010326 {_142062 _142063 _142064 : Type'} (t' : type24 _142062 _142064) (_105666 : cart _142062 _142063) (s : type24 _142062 _142063) (_105667 : cart _142062 _142064) (t : type24 _142062 _142064) : ((term510 _142062 _142063 _142064 _105666 s t _105667 t') = (term534 _142062 _142063 _142064 t' _105666 s _105667 t)) = ((term534 _142062 _142063 _142064 t' _105666 s _105667 t) = (term534 _142062 _142063 _142064 t' _105666 s _105667 t)).
Proof. exact (MK_COMB (@lem8010309 _142062 _142063 _142064 t' _105666 s _105667 t) (@lem8010325 _142062 _142063 _142064 t' _105666 s _105667 t)). Qed.
Lemma lem8010328 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8010329 (x : Prop) : (x = x) = True.
Proof. exact (@lem8010328 Prop x). Qed.
Lemma lem8010330 {_142062 _142063 _142064 : Type'} (t' : type24 _142062 _142064) (_105666 : cart _142062 _142063) (s : type24 _142062 _142063) (_105667 : cart _142062 _142064) (t : type24 _142062 _142064) : ((term534 _142062 _142063 _142064 t' _105666 s _105667 t) = (term534 _142062 _142063 _142064 t' _105666 s _105667 t)) = True.
Proof. exact (@lem8010329 (term534 _142062 _142063 _142064 t' _105666 s _105667 t)). Qed.
Lemma lem8010331 {_142062 _142063 _142064 : Type'} (t' : type24 _142062 _142064) (_105666 : cart _142062 _142063) (s : type24 _142062 _142063) (_105667 : cart _142062 _142064) (t : type24 _142062 _142064) : ((term510 _142062 _142063 _142064 _105666 s t _105667 t') = (term534 _142062 _142063 _142064 t' _105666 s _105667 t)) = True.
Proof. exact (TRANS (@lem8010326 _142062 _142063 _142064 t' _105666 s _105667 t) (@lem8010330 _142062 _142063 _142064 t' _105666 s _105667 t)). Qed.
Lemma lem8010332 {_142062 _142063 _142064 : Type'} (t' : type24 _142062 _142064) (_105666 : cart _142062 _142063) (s : type24 _142062 _142063) (_105667 : cart _142062 _142064) (t : type24 _142062 _142064) : True = ((term510 _142062 _142063 _142064 _105666 s t _105667 t') = (term534 _142062 _142063 _142064 t' _105666 s _105667 t)).
Proof. exact (SYM (@lem8010331 _142062 _142063 _142064 t' _105666 s _105667 t)). Qed.
Lemma lem8010333 {_142062 _142063 _142064 : Type'} (t' : type24 _142062 _142064) (_105666 : cart _142062 _142063) (s : type24 _142062 _142063) (_105667 : cart _142062 _142064) (t : type24 _142062 _142064) : (term510 _142062 _142063 _142064 _105666 s t _105667 t') = (term534 _142062 _142063 _142064 t' _105666 s _105667 t).
Proof. exact (EQ_MP (@lem8010332 _142062 _142063 _142064 t' _105666 s _105667 t) (@lem0)). Qed.
Lemma lem8010334 {_142062 _142063 _142064 : Type'} (_105666 : cart _142062 _142063) (_105667 : cart _142062 _142064) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : term534 _142062 _142063 _142064 t' _105666 s _105667 t.
Proof. exact (EQ_MP (@lem8010333 _142062 _142063 _142064 t' _105666 s _105667 t) (@lem8010043 _142062 _142063 _142064 _105666 _105667 x y s x' s' t x'' t' h1)). Qed.
Lemma lem8010336 (b : Prop) (a : Prop) : (a \/ b) = (term520 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8010337 {_142062 _142063 _142064 : Type'} (_105666 : cart _142062 _142063) (s : type24 _142062 _142063) (t : type24 _142062 _142064) (_105667 : cart _142062 _142064) (t' : type24 _142062 _142064) : (term534 _142062 _142063 _142064 t' _105666 s _105667 t) = (term537 _142062 _142063 _142064 _105666 s t _105667 t').
Proof. exact (@lem8010336 (term115 _142062 _142063 _142064 _105666 s _105667 t) (@IN (cart _142062 _142064) _105667 t')). Qed.
Lemma lem8010339 (a : Prop) (b : Prop) : (term522 a b) = (term523 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8010340 {_142062 _142063 _142064 : Type'} (_105666 : cart _142062 _142063) (s : type24 _142062 _142063) (_105667 : cart _142062 _142064) (t : type24 _142062 _142064) : (term524 _142062 _142063 _142064 _105666 s _105667 t) = (term525 _142062 _142063 _142064 _105666 s _105667 t).
Proof. exact (@lem8010339 (term71 _142062 _142063 _105666 s) (term71 _142062 _142064 _105667 t)). Qed.
Lemma lem8010342 (a : Prop) : (term109 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8010343 {_142062 _142063 : Type'} (_105666 : cart _142062 _142063) (s : type24 _142062 _142063) : (term144 _142062 _142063 _105666 s) = (@IN (cart _142062 _142063) _105666 s).
Proof. exact (@lem8010342 (@IN (cart _142062 _142063) _105666 s)). Qed.
Lemma lem8010344 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8010345 {_142062 _142063 : Type'} (_105666 : cart _142062 _142063) (s : type24 _142062 _142063) : (term526 _142062 _142063 _105666 s) = (term241 _142062 _142063 _105666 s).
Proof. exact (MK_COMB (@lem8010344) (@lem8010343 _142062 _142063 _105666 s)). Qed.
Lemma lem8010347 (a : Prop) : (term109 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8010348 {_142062 _142064 : Type'} (_105667 : cart _142062 _142064) (t : type24 _142062 _142064) : (term144 _142062 _142064 _105667 t) = (@IN (cart _142062 _142064) _105667 t).
Proof. exact (@lem8010347 (@IN (cart _142062 _142064) _105667 t)). Qed.
Lemma lem8010349 {_142062 _142063 _142064 : Type'} (_105666 : cart _142062 _142063) (s : type24 _142062 _142063) (_105667 : cart _142062 _142064) (t : type24 _142062 _142064) : (term525 _142062 _142063 _142064 _105666 s _105667 t) = (term18 _142062 _142063 _142064 _105666 s _105667 t).
Proof. exact (MK_COMB (@lem8010345 _142062 _142063 _105666 s) (@lem8010348 _142062 _142064 _105667 t)). Qed.
Lemma lem8010350 {_142062 _142063 _142064 : Type'} (_105666 : cart _142062 _142063) (s : type24 _142062 _142063) (_105667 : cart _142062 _142064) (t : type24 _142062 _142064) : (term524 _142062 _142063 _142064 _105666 s _105667 t) = (term18 _142062 _142063 _142064 _105666 s _105667 t).
Proof. exact (TRANS (@lem8010340 _142062 _142063 _142064 _105666 s _105667 t) (@lem8010349 _142062 _142063 _142064 _105666 s _105667 t)). Qed.
Lemma lem8010351 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8010352 {_142062 _142063 _142064 : Type'} (_105666 : cart _142062 _142063) (s : type24 _142062 _142063) (_105667 : cart _142062 _142064) (t : type24 _142062 _142064) : (term527 _142062 _142063 _142064 _105666 s _105667 t) = (term528 _142062 _142063 _142064 _105666 s _105667 t).
Proof. exact (MK_COMB (@lem8010351) (@lem8010350 _142062 _142063 _142064 _105666 s _105667 t)). Qed.
Lemma lem8010353 {_142062 _142064 : Type'} (_105667 : cart _142062 _142064) (t' : type24 _142062 _142064) : (@IN (cart _142062 _142064) _105667 t') = (@IN (cart _142062 _142064) _105667 t').
Proof. exact (eq_refl (@IN (cart _142062 _142064) _105667 t')). Qed.
Lemma lem8010354 {_142062 _142063 _142064 : Type'} (_105666 : cart _142062 _142063) (s : type24 _142062 _142063) (t : type24 _142062 _142064) (_105667 : cart _142062 _142064) (t' : type24 _142062 _142064) : (term537 _142062 _142063 _142064 _105666 s t _105667 t') = (term538 _142062 _142063 _142064 _105666 s t _105667 t').
Proof. exact (MK_COMB (@lem8010352 _142062 _142063 _142064 _105666 s _105667 t) (@lem8010353 _142062 _142064 _105667 t')). Qed.
Lemma lem8010355 {_142062 _142063 _142064 : Type'} (_105666 : cart _142062 _142063) (s : type24 _142062 _142063) (t : type24 _142062 _142064) (_105667 : cart _142062 _142064) (t' : type24 _142062 _142064) : (term534 _142062 _142063 _142064 t' _105666 s _105667 t) = (term538 _142062 _142063 _142064 _105666 s t _105667 t').
Proof. exact (TRANS (@lem8010337 _142062 _142063 _142064 _105666 s t _105667 t') (@lem8010354 _142062 _142063 _142064 _105666 s t _105667 t')). Qed.
Lemma lem8010357 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') (h2 : term153 _142062 _142064 t x'' t') : term18 _142062 _142063 _142064 x s x'' t.
Proof. exact (conj (@lem8010255 _142062 _142063 _142064 x y s x' s' t x'' t' h1) (@lem8010262 _142062 _142064 t x'' t' h2)). Qed.
Lemma lem8010359 {_142062 _142063 _142064 : Type'} (_105666 : cart _142062 _142063) (_105667 : cart _142062 _142064) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : term538 _142062 _142063 _142064 _105666 s t _105667 t'.
Proof. exact (EQ_MP (@lem8010355 _142062 _142063 _142064 _105666 s t _105667 t') (@lem8010334 _142062 _142063 _142064 _105666 _105667 x y s x' s' t x'' t' h1)). Qed.
Lemma lem8010360 {_142062 _142063 _142064 : Type'} (_105666 : cart _142062 _142063) (_105667 : cart _142062 _142064) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : term538 _142062 _142063 _142064 _105666 s t _105667 t'.
Proof. exact (@lem8010359 _142062 _142063 _142064 _105666 _105667 x y s x' s' t x'' t' h1). Qed.
Lemma lem8010361 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : term538 _142062 _142063 _142064 x s t x'' t'.
Proof. exact (@lem8010360 _142062 _142063 _142064 x x'' x y s x' s' t x'' t' h1). Qed.
Lemma lem8010364 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') (h2 : term153 _142062 _142064 t x'' t') : @IN (cart _142062 _142064) x'' t'.
Proof. exact (@lem8010361 _142062 _142063 _142064 x y s x' s' t x'' t' h1 (@lem8010357 _142062 _142063 _142064 x y s x' s' t x'' t' h1 h2)). Qed.
Lemma lem8010365 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') (h2 : term153 _142062 _142064 t x'' t') : term511 _142062 _142064 x'' t'.
Proof. exact (fun h0 : term71 _142062 _142064 x'' t' => @lem8010364 _142062 _142063 _142064 x y s x' s' t x'' t' h1 h2). Qed.
Lemma lem8010367 (p : Prop) : (term512 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8010368 {_142062 _142064 : Type'} (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) : (term511 _142062 _142064 x'' t') = (@IN (cart _142062 _142064) x'' t').
Proof. exact (@lem8010367 (@IN (cart _142062 _142064) x'' t')). Qed.
Lemma lem8010369 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') (h2 : term153 _142062 _142064 t x'' t') : @IN (cart _142062 _142064) x'' t'.
Proof. exact (EQ_MP (@lem8010368 _142062 _142064 x'' t') (@lem8010365 _142062 _142063 _142064 x y s x' s' t x'' t' h1 h2)). Qed.
Lemma lem8010372 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8010374 {_142062 _142064 : Type'} (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) : (term71 _142062 _142064 x'' t') = (term530 _142062 _142064 x'' t').
Proof. exact (@lem8010372 (@IN (cart _142062 _142064) x'' t')). Qed.
Lemma lem8010377 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term153 _142062 _142064 t x'' t') : term530 _142062 _142064 x'' t'.
Proof. exact (EQ_MP (@lem8010374 _142062 _142064 x'' t') (@lem8010019 _142062 _142064 t x'' t' h1)). Qed.
Lemma lem8010380 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') (h2 : term153 _142062 _142064 t x'' t') : False.
Proof. exact (@lem8010377 _142062 _142064 t x'' t' h2 (@lem8010369 _142062 _142063 _142064 x y s x' s' t x'' t' h1 h2)). Qed.
Lemma lem8010381 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') (h2 : term153 _142062 _142064 t x'' t') : term531.
Proof. exact (fun h0 : ~ False => @lem8010380 _142062 _142063 _142064 x y s x' s' t x'' t' h1 h2). Qed.
Lemma lem8010383 (p : Prop) : (term512 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8010384 : term531 = False.
Proof. exact (@lem8010383 False). Qed.
Lemma lem8010385 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') (h2 : term153 _142062 _142064 t x'' t') : False.
Proof. exact (EQ_MP (@lem8010384) (@lem8010381 _142062 _142063 _142064 x y s x' s' t x'' t' h1 h2)). Qed.
Lemma lem8010387 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term413 _142062 _142063 _142064 x y s s' t t') : @IN (cart _142062 _142063) x s.
Proof. exact (proj1 (@lem8009675 _142062 _142063 _142064 x y s s' t t' h1)). Qed.
Lemma lem8010388 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term413 _142062 _142063 _142064 x y s s' t t') : term511 _142062 _142063 x s.
Proof. exact (fun h0 : term71 _142062 _142063 x s => @lem8010387 _142062 _142063 _142064 x y s s' t t' h1). Qed.
Lemma lem8010390 (p : Prop) : (term512 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8010391 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) : (term511 _142062 _142063 x s) = (@IN (cart _142062 _142063) x s).
Proof. exact (@lem8010390 (@IN (cart _142062 _142063) x s)). Qed.
Lemma lem8010392 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term413 _142062 _142063 _142064 x y s s' t t') : @IN (cart _142062 _142063) x s.
Proof. exact (EQ_MP (@lem8010391 _142062 _142063 x s) (@lem8010388 _142062 _142063 _142064 x y s s' t t' h1)). Qed.
Lemma lem8010395 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8010397 {_142062 _142063 : Type'} (_105668 : cart _142062 _142063) (s : type24 _142062 _142063) : (term71 _142062 _142063 _105668 s) = (term530 _142062 _142063 _105668 s).
Proof. exact (@lem8010395 (@IN (cart _142062 _142063) _105668 s)). Qed.
Lemma lem8010400 {_142062 _142063 : Type'} (_105668 : cart _142062 _142063) (s : type24 _142062 _142063) (h1 : term74 _142062 _142063 s) : term530 _142062 _142063 _105668 s.
Proof. exact (EQ_MP (@lem8010397 _142062 _142063 _105668 s) (@lem8010051 _142062 _142063 _105668 s h1)). Qed.
Lemma lem8010401 {_142062 _142063 : Type'} (_105668 : cart _142062 _142063) (s : type24 _142062 _142063) (h1 : term74 _142062 _142063 s) : term530 _142062 _142063 _105668 s.
Proof. exact (@lem8010400 _142062 _142063 _105668 s h1). Qed.
Lemma lem8010402 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (h1 : term74 _142062 _142063 s) : term530 _142062 _142063 x s.
Proof. exact (@lem8010401 _142062 _142063 x s h1). Qed.
Lemma lem8010405 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term74 _142062 _142063 s) (h2 : term413 _142062 _142063 _142064 x y s s' t t') : False.
Proof. exact (@lem8010402 _142062 _142063 x s h1 (@lem8010392 _142062 _142063 _142064 x y s s' t t' h2)). Qed.
Lemma lem8010406 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term74 _142062 _142063 s) (h2 : term413 _142062 _142063 _142064 x y s s' t t') : term531.
Proof. exact (fun h0 : ~ False => @lem8010405 _142062 _142063 _142064 x y s s' t t' h1 h2). Qed.
Lemma lem8010408 (p : Prop) : (term512 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8010409 : term531 = False.
Proof. exact (@lem8010408 False). Qed.
Lemma lem8010410 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term74 _142062 _142063 s) (h2 : term413 _142062 _142063 _142064 x y s s' t t') : False.
Proof. exact (EQ_MP (@lem8010409) (@lem8010406 _142062 _142063 _142064 x y s s' t t' h1 h2)). Qed.
Lemma lem8010412 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term413 _142062 _142063 _142064 x y s s' t t') : @IN (cart _142062 _142064) y t.
Proof. exact (proj2 (@lem8009675 _142062 _142063 _142064 x y s s' t t' h1)). Qed.
Lemma lem8010413 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term413 _142062 _142063 _142064 x y s s' t t') : term511 _142062 _142064 y t.
Proof. exact (fun h0 : term71 _142062 _142064 y t => @lem8010412 _142062 _142063 _142064 x y s s' t t' h1). Qed.
Lemma lem8010415 (p : Prop) : (term512 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8010416 {_142062 _142064 : Type'} (y : cart _142062 _142064) (t : type24 _142062 _142064) : (term511 _142062 _142064 y t) = (@IN (cart _142062 _142064) y t).
Proof. exact (@lem8010415 (@IN (cart _142062 _142064) y t)). Qed.
Lemma lem8010417 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term413 _142062 _142063 _142064 x y s s' t t') : @IN (cart _142062 _142064) y t.
Proof. exact (EQ_MP (@lem8010416 _142062 _142064 y t) (@lem8010413 _142062 _142063 _142064 x y s s' t t' h1)). Qed.
Lemma lem8010420 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8010422 {_142062 _142064 : Type'} (_105669 : cart _142062 _142064) (t : type24 _142062 _142064) : (term71 _142062 _142064 _105669 t) = (term530 _142062 _142064 _105669 t).
Proof. exact (@lem8010420 (@IN (cart _142062 _142064) _105669 t)). Qed.
Lemma lem8010425 {_142062 _142064 : Type'} (_105669 : cart _142062 _142064) (t : type24 _142062 _142064) (h1 : term74 _142062 _142064 t) : term530 _142062 _142064 _105669 t.
Proof. exact (EQ_MP (@lem8010422 _142062 _142064 _105669 t) (@lem8010059 _142062 _142064 _105669 t h1)). Qed.
Lemma lem8010426 {_142062 _142064 : Type'} (_105669 : cart _142062 _142064) (t : type24 _142062 _142064) (h1 : term74 _142062 _142064 t) : term530 _142062 _142064 _105669 t.
Proof. exact (@lem8010425 _142062 _142064 _105669 t h1). Qed.
Lemma lem8010427 {_142062 _142064 : Type'} (y : cart _142062 _142064) (t : type24 _142062 _142064) (h1 : term74 _142062 _142064 t) : term530 _142062 _142064 y t.
Proof. exact (@lem8010426 _142062 _142064 y t h1). Qed.
Lemma lem8010430 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term74 _142062 _142064 t) (h2 : term413 _142062 _142063 _142064 x y s s' t t') : False.
Proof. exact (@lem8010427 _142062 _142064 y t h1 (@lem8010417 _142062 _142063 _142064 x y s s' t t' h2)). Qed.
Lemma lem8010431 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term74 _142062 _142064 t) (h2 : term413 _142062 _142063 _142064 x y s s' t t') : term531.
Proof. exact (fun h0 : ~ False => @lem8010430 _142062 _142063 _142064 x y s s' t t' h1 h2). Qed.
Lemma lem8010433 (p : Prop) : (term512 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8010434 : term531 = False.
Proof. exact (@lem8010433 False). Qed.
Lemma lem8010435 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term74 _142062 _142064 t) (h2 : term413 _142062 _142063 _142064 x y s s' t t') : False.
Proof. exact (EQ_MP (@lem8010434) (@lem8010431 _142062 _142063 _142064 x y s s' t t' h1 h2)). Qed.
Lemma lem8010437 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term413 _142062 _142063 _142064 x y s s' t t') : @IN (cart _142062 _142063) x s.
Proof. exact (proj1 (@lem8009675 _142062 _142063 _142064 x y s s' t t' h1)). Qed.
Lemma lem8010438 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term413 _142062 _142063 _142064 x y s s' t t') : term511 _142062 _142063 x s.
Proof. exact (fun h0 : term71 _142062 _142063 x s => @lem8010437 _142062 _142063 _142064 x y s s' t t' h1). Qed.
Lemma lem8010440 (p : Prop) : (term512 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8010441 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) : (term511 _142062 _142063 x s) = (@IN (cart _142062 _142063) x s).
Proof. exact (@lem8010440 (@IN (cart _142062 _142063) x s)). Qed.
Lemma lem8010442 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term413 _142062 _142063 _142064 x y s s' t t') : @IN (cart _142062 _142063) x s.
Proof. exact (EQ_MP (@lem8010441 _142062 _142063 x s) (@lem8010438 _142062 _142063 _142064 x y s s' t t' h1)). Qed.
Lemma lem8010448 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8010449 {_142062 _142063 : Type'} (s' : type24 _142062 _142063) (_105670 : cart _142062 _142063) (s : type24 _142062 _142063) : (term154 _142062 _142063 s _105670 s') = (term532 _142062 _142063 s' _105670 s).
Proof. exact (@lem8010448 (@IN (cart _142062 _142063) _105670 s') (term71 _142062 _142063 _105670 s)). Qed.
Lemma lem8010455 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8010456 {_142062 _142063 : Type'} (s' : type24 _142062 _142063) (_105670 : cart _142062 _142063) (s : type24 _142062 _142063) : (term539 _142062 _142063 s _105670 s') = (term540 _142062 _142063 s' _105670 s).
Proof. exact (MK_COMB (@lem8010455) (@lem8010449 _142062 _142063 s' _105670 s)). Qed.
Lemma lem8010462 {_142062 _142063 : Type'} (s' : type24 _142062 _142063) (_105670 : cart _142062 _142063) (s : type24 _142062 _142063) : (term532 _142062 _142063 s' _105670 s) = (term532 _142062 _142063 s' _105670 s).
Proof. exact (eq_refl (term532 _142062 _142063 s' _105670 s)). Qed.
Lemma lem8010463 {_142062 _142063 : Type'} (s' : type24 _142062 _142063) (_105670 : cart _142062 _142063) (s : type24 _142062 _142063) : ((term154 _142062 _142063 s _105670 s') = (term532 _142062 _142063 s' _105670 s)) = ((term532 _142062 _142063 s' _105670 s) = (term532 _142062 _142063 s' _105670 s)).
Proof. exact (MK_COMB (@lem8010456 _142062 _142063 s' _105670 s) (@lem8010462 _142062 _142063 s' _105670 s)). Qed.
Lemma lem8010465 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8010466 (x : Prop) : (x = x) = True.
Proof. exact (@lem8010465 Prop x). Qed.
Lemma lem8010467 {_142062 _142063 : Type'} (s' : type24 _142062 _142063) (_105670 : cart _142062 _142063) (s : type24 _142062 _142063) : ((term532 _142062 _142063 s' _105670 s) = (term532 _142062 _142063 s' _105670 s)) = True.
Proof. exact (@lem8010466 (term532 _142062 _142063 s' _105670 s)). Qed.
Lemma lem8010468 {_142062 _142063 : Type'} (s' : type24 _142062 _142063) (_105670 : cart _142062 _142063) (s : type24 _142062 _142063) : ((term154 _142062 _142063 s _105670 s') = (term532 _142062 _142063 s' _105670 s)) = True.
Proof. exact (TRANS (@lem8010463 _142062 _142063 s' _105670 s) (@lem8010467 _142062 _142063 s' _105670 s)). Qed.
Lemma lem8010469 {_142062 _142063 : Type'} (s' : type24 _142062 _142063) (_105670 : cart _142062 _142063) (s : type24 _142062 _142063) : True = ((term154 _142062 _142063 s _105670 s') = (term532 _142062 _142063 s' _105670 s)).
Proof. exact (SYM (@lem8010468 _142062 _142063 s' _105670 s)). Qed.
Lemma lem8010470 {_142062 _142063 : Type'} (s' : type24 _142062 _142063) (_105670 : cart _142062 _142063) (s : type24 _142062 _142063) : (term154 _142062 _142063 s _105670 s') = (term532 _142062 _142063 s' _105670 s).
Proof. exact (EQ_MP (@lem8010469 _142062 _142063 s' _105670 s) (@lem0)). Qed.
Lemma lem8010471 {_142062 _142063 _142064 : Type'} (_105670 : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term170 _142062 _142063 _142064 s s' t t') : term532 _142062 _142063 s' _105670 s.
Proof. exact (EQ_MP (@lem8010470 _142062 _142063 s' _105670 s) (@lem8010071 _142062 _142063 _142064 _105670 s s' t t' h1)). Qed.
Lemma lem8010473 (b : Prop) (a : Prop) : (a \/ b) = (term520 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8010474 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (_105670 : cart _142062 _142063) (s' : type24 _142062 _142063) : (term532 _142062 _142063 s' _105670 s) = (term541 _142062 _142063 s _105670 s').
Proof. exact (@lem8010473 (term71 _142062 _142063 _105670 s) (@IN (cart _142062 _142063) _105670 s')). Qed.
Lemma lem8010476 (a : Prop) : (term109 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8010477 {_142062 _142063 : Type'} (_105670 : cart _142062 _142063) (s : type24 _142062 _142063) : (term144 _142062 _142063 _105670 s) = (@IN (cart _142062 _142063) _105670 s).
Proof. exact (@lem8010476 (@IN (cart _142062 _142063) _105670 s)). Qed.
Lemma lem8010478 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8010479 {_142062 _142063 : Type'} (_105670 : cart _142062 _142063) (s : type24 _142062 _142063) : (term542 _142062 _142063 _105670 s) = (term543 _142062 _142063 _105670 s).
Proof. exact (MK_COMB (@lem8010478) (@lem8010477 _142062 _142063 _105670 s)). Qed.
Lemma lem8010480 {_142062 _142063 : Type'} (_105670 : cart _142062 _142063) (s' : type24 _142062 _142063) : (@IN (cart _142062 _142063) _105670 s') = (@IN (cart _142062 _142063) _105670 s').
Proof. exact (eq_refl (@IN (cart _142062 _142063) _105670 s')). Qed.
Lemma lem8010481 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (_105670 : cart _142062 _142063) (s' : type24 _142062 _142063) : (term541 _142062 _142063 s _105670 s') = (term110 _142062 _142063 s _105670 s').
Proof. exact (MK_COMB (@lem8010479 _142062 _142063 _105670 s) (@lem8010480 _142062 _142063 _105670 s')). Qed.
Lemma lem8010482 {_142062 _142063 : Type'} (s : type24 _142062 _142063) (_105670 : cart _142062 _142063) (s' : type24 _142062 _142063) : (term532 _142062 _142063 s' _105670 s) = (term110 _142062 _142063 s _105670 s').
Proof. exact (TRANS (@lem8010474 _142062 _142063 s _105670 s') (@lem8010481 _142062 _142063 s _105670 s')). Qed.
Lemma lem8010485 {_142062 _142063 _142064 : Type'} (_105670 : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term170 _142062 _142063 _142064 s s' t t') : term110 _142062 _142063 s _105670 s'.
Proof. exact (EQ_MP (@lem8010482 _142062 _142063 s _105670 s') (@lem8010471 _142062 _142063 _142064 _105670 s s' t t' h1)). Qed.
Lemma lem8010486 {_142062 _142063 _142064 : Type'} (_105670 : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term170 _142062 _142063 _142064 s s' t t') : term110 _142062 _142063 s _105670 s'.
Proof. exact (@lem8010485 _142062 _142063 _142064 _105670 s s' t t' h1). Qed.
Lemma lem8010487 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term170 _142062 _142063 _142064 s s' t t') : term110 _142062 _142063 s x s'.
Proof. exact (@lem8010486 _142062 _142063 _142064 x s s' t t' h1). Qed.
Lemma lem8010490 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term170 _142062 _142063 _142064 s s' t t') (h2 : term413 _142062 _142063 _142064 x y s s' t t') : @IN (cart _142062 _142063) x s'.
Proof. exact (@lem8010487 _142062 _142063 _142064 x s s' t t' h1 (@lem8010442 _142062 _142063 _142064 x y s s' t t' h2)). Qed.
Lemma lem8010491 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term170 _142062 _142063 _142064 s s' t t') (h2 : term413 _142062 _142063 _142064 x y s s' t t') : term511 _142062 _142063 x s'.
Proof. exact (fun h0 : term71 _142062 _142063 x s' => @lem8010490 _142062 _142063 _142064 x y s s' t t' h1 h2). Qed.
Lemma lem8010493 (p : Prop) : (term512 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8010494 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s' : type24 _142062 _142063) : (term511 _142062 _142063 x s') = (@IN (cart _142062 _142063) x s').
Proof. exact (@lem8010493 (@IN (cart _142062 _142063) x s')). Qed.
Lemma lem8010495 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term170 _142062 _142063 _142064 s s' t t') (h2 : term413 _142062 _142063 _142064 x y s s' t t') : @IN (cart _142062 _142063) x s'.
Proof. exact (EQ_MP (@lem8010494 _142062 _142063 x s') (@lem8010491 _142062 _142063 _142064 x y s s' t t' h1 h2)). Qed.
Lemma lem8010498 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8010500 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s' : type24 _142062 _142063) : (term71 _142062 _142063 x s') = (term530 _142062 _142063 x s').
Proof. exact (@lem8010498 (@IN (cart _142062 _142063) x s')). Qed.
Lemma lem8010503 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s' : type24 _142062 _142063) (h1 : term71 _142062 _142063 x s') : term530 _142062 _142063 x s'.
Proof. exact (EQ_MP (@lem8010500 _142062 _142063 x s') (@lem8010065 _142062 _142063 x s' h1)). Qed.
Lemma lem8010506 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term71 _142062 _142063 x s') (h2 : term170 _142062 _142063 _142064 s s' t t') (h3 : term413 _142062 _142063 _142064 x y s s' t t') : False.
Proof. exact (@lem8010503 _142062 _142063 x s' h1 (@lem8010495 _142062 _142063 _142064 x y s s' t t' h2 h3)). Qed.
Lemma lem8010507 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term71 _142062 _142063 x s') (h2 : term170 _142062 _142063 _142064 s s' t t') (h3 : term413 _142062 _142063 _142064 x y s s' t t') : term531.
Proof. exact (fun h0 : ~ False => @lem8010506 _142062 _142063 _142064 x y s s' t t' h1 h2 h3). Qed.
Lemma lem8010509 (p : Prop) : (term512 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8010510 : term531 = False.
Proof. exact (@lem8010509 False). Qed.
Lemma lem8010511 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term71 _142062 _142063 x s') (h2 : term170 _142062 _142063 _142064 s s' t t') (h3 : term413 _142062 _142063 _142064 x y s s' t t') : False.
Proof. exact (EQ_MP (@lem8010510) (@lem8010507 _142062 _142063 _142064 x y s s' t t' h1 h2 h3)). Qed.
Lemma lem8010513 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term413 _142062 _142063 _142064 x y s s' t t') : @IN (cart _142062 _142063) x s.
Proof. exact (proj1 (@lem8009675 _142062 _142063 _142064 x y s s' t t' h1)). Qed.
Lemma lem8010514 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term413 _142062 _142063 _142064 x y s s' t t') : term511 _142062 _142063 x s.
Proof. exact (fun h0 : term71 _142062 _142063 x s => @lem8010513 _142062 _142063 _142064 x y s s' t t' h1). Qed.
Lemma lem8010516 (p : Prop) : (term512 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8010517 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) : (term511 _142062 _142063 x s) = (@IN (cart _142062 _142063) x s).
Proof. exact (@lem8010516 (@IN (cart _142062 _142063) x s)). Qed.
Lemma lem8010518 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term413 _142062 _142063 _142064 x y s s' t t') : @IN (cart _142062 _142063) x s.
Proof. exact (EQ_MP (@lem8010517 _142062 _142063 x s) (@lem8010514 _142062 _142063 _142064 x y s s' t t' h1)). Qed.
Lemma lem8010521 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8010523 {_142062 _142063 : Type'} (_105672 : cart _142062 _142063) (s : type24 _142062 _142063) : (term71 _142062 _142063 _105672 s) = (term530 _142062 _142063 _105672 s).
Proof. exact (@lem8010521 (@IN (cart _142062 _142063) _105672 s)). Qed.
Lemma lem8010526 {_142062 _142063 : Type'} (_105672 : cart _142062 _142063) (s : type24 _142062 _142063) (h1 : term74 _142062 _142063 s) : term530 _142062 _142063 _105672 s.
Proof. exact (EQ_MP (@lem8010523 _142062 _142063 _105672 s) (@lem8010085 _142062 _142063 _105672 s h1)). Qed.
Lemma lem8010527 {_142062 _142063 : Type'} (_105672 : cart _142062 _142063) (s : type24 _142062 _142063) (h1 : term74 _142062 _142063 s) : term530 _142062 _142063 _105672 s.
Proof. exact (@lem8010526 _142062 _142063 _105672 s h1). Qed.
Lemma lem8010528 {_142062 _142063 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (h1 : term74 _142062 _142063 s) : term530 _142062 _142063 x s.
Proof. exact (@lem8010527 _142062 _142063 x s h1). Qed.
Lemma lem8010531 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term74 _142062 _142063 s) (h2 : term413 _142062 _142063 _142064 x y s s' t t') : False.
Proof. exact (@lem8010528 _142062 _142063 x s h1 (@lem8010518 _142062 _142063 _142064 x y s s' t t' h2)). Qed.
Lemma lem8010532 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term74 _142062 _142063 s) (h2 : term413 _142062 _142063 _142064 x y s s' t t') : term531.
Proof. exact (fun h0 : ~ False => @lem8010531 _142062 _142063 _142064 x y s s' t t' h1 h2). Qed.
Lemma lem8010534 (p : Prop) : (term512 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8010535 : term531 = False.
Proof. exact (@lem8010534 False). Qed.
Lemma lem8010536 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term74 _142062 _142063 s) (h2 : term413 _142062 _142063 _142064 x y s s' t t') : False.
Proof. exact (EQ_MP (@lem8010535) (@lem8010532 _142062 _142063 _142064 x y s s' t t' h1 h2)). Qed.
Lemma lem8010538 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term413 _142062 _142063 _142064 x y s s' t t') : @IN (cart _142062 _142064) y t.
Proof. exact (proj2 (@lem8009675 _142062 _142063 _142064 x y s s' t t' h1)). Qed.
Lemma lem8010539 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term413 _142062 _142063 _142064 x y s s' t t') : term511 _142062 _142064 y t.
Proof. exact (fun h0 : term71 _142062 _142064 y t => @lem8010538 _142062 _142063 _142064 x y s s' t t' h1). Qed.
Lemma lem8010541 (p : Prop) : (term512 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8010542 {_142062 _142064 : Type'} (y : cart _142062 _142064) (t : type24 _142062 _142064) : (term511 _142062 _142064 y t) = (@IN (cart _142062 _142064) y t).
Proof. exact (@lem8010541 (@IN (cart _142062 _142064) y t)). Qed.
Lemma lem8010543 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term413 _142062 _142063 _142064 x y s s' t t') : @IN (cart _142062 _142064) y t.
Proof. exact (EQ_MP (@lem8010542 _142062 _142064 y t) (@lem8010539 _142062 _142063 _142064 x y s s' t t' h1)). Qed.
Lemma lem8010546 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8010548 {_142062 _142064 : Type'} (_105673 : cart _142062 _142064) (t : type24 _142062 _142064) : (term71 _142062 _142064 _105673 t) = (term530 _142062 _142064 _105673 t).
Proof. exact (@lem8010546 (@IN (cart _142062 _142064) _105673 t)). Qed.
Lemma lem8010551 {_142062 _142064 : Type'} (_105673 : cart _142062 _142064) (t : type24 _142062 _142064) (h1 : term74 _142062 _142064 t) : term530 _142062 _142064 _105673 t.
Proof. exact (EQ_MP (@lem8010548 _142062 _142064 _105673 t) (@lem8010093 _142062 _142064 _105673 t h1)). Qed.
Lemma lem8010552 {_142062 _142064 : Type'} (_105673 : cart _142062 _142064) (t : type24 _142062 _142064) (h1 : term74 _142062 _142064 t) : term530 _142062 _142064 _105673 t.
Proof. exact (@lem8010551 _142062 _142064 _105673 t h1). Qed.
Lemma lem8010553 {_142062 _142064 : Type'} (y : cart _142062 _142064) (t : type24 _142062 _142064) (h1 : term74 _142062 _142064 t) : term530 _142062 _142064 y t.
Proof. exact (@lem8010552 _142062 _142064 y t h1). Qed.
Lemma lem8010556 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term74 _142062 _142064 t) (h2 : term413 _142062 _142063 _142064 x y s s' t t') : False.
Proof. exact (@lem8010553 _142062 _142064 y t h1 (@lem8010543 _142062 _142063 _142064 x y s s' t t' h2)). Qed.
Lemma lem8010557 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term74 _142062 _142064 t) (h2 : term413 _142062 _142063 _142064 x y s s' t t') : term531.
Proof. exact (fun h0 : ~ False => @lem8010556 _142062 _142063 _142064 x y s s' t t' h1 h2). Qed.
Lemma lem8010559 (p : Prop) : (term512 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8010560 : term531 = False.
Proof. exact (@lem8010559 False). Qed.
Lemma lem8010561 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term74 _142062 _142064 t) (h2 : term413 _142062 _142063 _142064 x y s s' t t') : False.
Proof. exact (EQ_MP (@lem8010560) (@lem8010557 _142062 _142063 _142064 x y s s' t t' h1 h2)). Qed.
Lemma lem8010563 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term413 _142062 _142063 _142064 x y s s' t t') : @IN (cart _142062 _142064) y t.
Proof. exact (proj2 (@lem8009675 _142062 _142063 _142064 x y s s' t t' h1)). Qed.
Lemma lem8010564 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term413 _142062 _142063 _142064 x y s s' t t') : term511 _142062 _142064 y t.
Proof. exact (fun h0 : term71 _142062 _142064 y t => @lem8010563 _142062 _142063 _142064 x y s s' t t' h1). Qed.
Lemma lem8010566 (p : Prop) : (term512 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8010567 {_142062 _142064 : Type'} (y : cart _142062 _142064) (t : type24 _142062 _142064) : (term511 _142062 _142064 y t) = (@IN (cart _142062 _142064) y t).
Proof. exact (@lem8010566 (@IN (cart _142062 _142064) y t)). Qed.
Lemma lem8010568 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term413 _142062 _142063 _142064 x y s s' t t') : @IN (cart _142062 _142064) y t.
Proof. exact (EQ_MP (@lem8010567 _142062 _142064 y t) (@lem8010564 _142062 _142063 _142064 x y s s' t t' h1)). Qed.
Lemma lem8010574 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8010575 {_142062 _142064 : Type'} (t' : type24 _142062 _142064) (_105675 : cart _142062 _142064) (t : type24 _142062 _142064) : (term154 _142062 _142064 t _105675 t') = (term532 _142062 _142064 t' _105675 t).
Proof. exact (@lem8010574 (@IN (cart _142062 _142064) _105675 t') (term71 _142062 _142064 _105675 t)). Qed.
Lemma lem8010581 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8010582 {_142062 _142064 : Type'} (t' : type24 _142062 _142064) (_105675 : cart _142062 _142064) (t : type24 _142062 _142064) : (term539 _142062 _142064 t _105675 t') = (term540 _142062 _142064 t' _105675 t).
Proof. exact (MK_COMB (@lem8010581) (@lem8010575 _142062 _142064 t' _105675 t)). Qed.
Lemma lem8010588 {_142062 _142064 : Type'} (t' : type24 _142062 _142064) (_105675 : cart _142062 _142064) (t : type24 _142062 _142064) : (term532 _142062 _142064 t' _105675 t) = (term532 _142062 _142064 t' _105675 t).
Proof. exact (eq_refl (term532 _142062 _142064 t' _105675 t)). Qed.
Lemma lem8010589 {_142062 _142064 : Type'} (t' : type24 _142062 _142064) (_105675 : cart _142062 _142064) (t : type24 _142062 _142064) : ((term154 _142062 _142064 t _105675 t') = (term532 _142062 _142064 t' _105675 t)) = ((term532 _142062 _142064 t' _105675 t) = (term532 _142062 _142064 t' _105675 t)).
Proof. exact (MK_COMB (@lem8010582 _142062 _142064 t' _105675 t) (@lem8010588 _142062 _142064 t' _105675 t)). Qed.
Lemma lem8010591 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8010592 (x : Prop) : (x = x) = True.
Proof. exact (@lem8010591 Prop x). Qed.
Lemma lem8010593 {_142062 _142064 : Type'} (t' : type24 _142062 _142064) (_105675 : cart _142062 _142064) (t : type24 _142062 _142064) : ((term532 _142062 _142064 t' _105675 t) = (term532 _142062 _142064 t' _105675 t)) = True.
Proof. exact (@lem8010592 (term532 _142062 _142064 t' _105675 t)). Qed.
Lemma lem8010594 {_142062 _142064 : Type'} (t' : type24 _142062 _142064) (_105675 : cart _142062 _142064) (t : type24 _142062 _142064) : ((term154 _142062 _142064 t _105675 t') = (term532 _142062 _142064 t' _105675 t)) = True.
Proof. exact (TRANS (@lem8010589 _142062 _142064 t' _105675 t) (@lem8010593 _142062 _142064 t' _105675 t)). Qed.
Lemma lem8010595 {_142062 _142064 : Type'} (t' : type24 _142062 _142064) (_105675 : cart _142062 _142064) (t : type24 _142062 _142064) : True = ((term154 _142062 _142064 t _105675 t') = (term532 _142062 _142064 t' _105675 t)).
Proof. exact (SYM (@lem8010594 _142062 _142064 t' _105675 t)). Qed.
Lemma lem8010596 {_142062 _142064 : Type'} (t' : type24 _142062 _142064) (_105675 : cart _142062 _142064) (t : type24 _142062 _142064) : (term154 _142062 _142064 t _105675 t') = (term532 _142062 _142064 t' _105675 t).
Proof. exact (EQ_MP (@lem8010595 _142062 _142064 t' _105675 t) (@lem0)). Qed.
Lemma lem8010597 {_142062 _142063 _142064 : Type'} (_105675 : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term170 _142062 _142063 _142064 s s' t t') : term532 _142062 _142064 t' _105675 t.
Proof. exact (EQ_MP (@lem8010596 _142062 _142064 t' _105675 t) (@lem8010111 _142062 _142063 _142064 _105675 s s' t t' h1)). Qed.
Lemma lem8010599 (b : Prop) (a : Prop) : (a \/ b) = (term520 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8010600 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (_105675 : cart _142062 _142064) (t' : type24 _142062 _142064) : (term532 _142062 _142064 t' _105675 t) = (term541 _142062 _142064 t _105675 t').
Proof. exact (@lem8010599 (term71 _142062 _142064 _105675 t) (@IN (cart _142062 _142064) _105675 t')). Qed.
Lemma lem8010602 (a : Prop) : (term109 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8010603 {_142062 _142064 : Type'} (_105675 : cart _142062 _142064) (t : type24 _142062 _142064) : (term144 _142062 _142064 _105675 t) = (@IN (cart _142062 _142064) _105675 t).
Proof. exact (@lem8010602 (@IN (cart _142062 _142064) _105675 t)). Qed.
Lemma lem8010604 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8010605 {_142062 _142064 : Type'} (_105675 : cart _142062 _142064) (t : type24 _142062 _142064) : (term542 _142062 _142064 _105675 t) = (term543 _142062 _142064 _105675 t).
Proof. exact (MK_COMB (@lem8010604) (@lem8010603 _142062 _142064 _105675 t)). Qed.
Lemma lem8010606 {_142062 _142064 : Type'} (_105675 : cart _142062 _142064) (t' : type24 _142062 _142064) : (@IN (cart _142062 _142064) _105675 t') = (@IN (cart _142062 _142064) _105675 t').
Proof. exact (eq_refl (@IN (cart _142062 _142064) _105675 t')). Qed.
Lemma lem8010607 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (_105675 : cart _142062 _142064) (t' : type24 _142062 _142064) : (term541 _142062 _142064 t _105675 t') = (term110 _142062 _142064 t _105675 t').
Proof. exact (MK_COMB (@lem8010605 _142062 _142064 _105675 t) (@lem8010606 _142062 _142064 _105675 t')). Qed.
Lemma lem8010608 {_142062 _142064 : Type'} (t : type24 _142062 _142064) (_105675 : cart _142062 _142064) (t' : type24 _142062 _142064) : (term532 _142062 _142064 t' _105675 t) = (term110 _142062 _142064 t _105675 t').
Proof. exact (TRANS (@lem8010600 _142062 _142064 t _105675 t') (@lem8010607 _142062 _142064 t _105675 t')). Qed.
Lemma lem8010611 {_142062 _142063 _142064 : Type'} (_105675 : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term170 _142062 _142063 _142064 s s' t t') : term110 _142062 _142064 t _105675 t'.
Proof. exact (EQ_MP (@lem8010608 _142062 _142064 t _105675 t') (@lem8010597 _142062 _142063 _142064 _105675 s s' t t' h1)). Qed.
Lemma lem8010612 {_142062 _142063 _142064 : Type'} (_105675 : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term170 _142062 _142063 _142064 s s' t t') : term110 _142062 _142064 t _105675 t'.
Proof. exact (@lem8010611 _142062 _142063 _142064 _105675 s s' t t' h1). Qed.
Lemma lem8010613 {_142062 _142063 _142064 : Type'} (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term170 _142062 _142063 _142064 s s' t t') : term110 _142062 _142064 t y t'.
Proof. exact (@lem8010612 _142062 _142063 _142064 y s s' t t' h1). Qed.
Lemma lem8010616 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term170 _142062 _142063 _142064 s s' t t') (h2 : term413 _142062 _142063 _142064 x y s s' t t') : @IN (cart _142062 _142064) y t'.
Proof. exact (@lem8010613 _142062 _142063 _142064 y s s' t t' h1 (@lem8010568 _142062 _142063 _142064 x y s s' t t' h2)). Qed.
Lemma lem8010617 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term170 _142062 _142063 _142064 s s' t t') (h2 : term413 _142062 _142063 _142064 x y s s' t t') : term511 _142062 _142064 y t'.
Proof. exact (fun h0 : term71 _142062 _142064 y t' => @lem8010616 _142062 _142063 _142064 x y s s' t t' h1 h2). Qed.
Lemma lem8010619 (p : Prop) : (term512 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8010620 {_142062 _142064 : Type'} (y : cart _142062 _142064) (t' : type24 _142062 _142064) : (term511 _142062 _142064 y t') = (@IN (cart _142062 _142064) y t').
Proof. exact (@lem8010619 (@IN (cart _142062 _142064) y t')). Qed.
Lemma lem8010621 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term170 _142062 _142063 _142064 s s' t t') (h2 : term413 _142062 _142063 _142064 x y s s' t t') : @IN (cart _142062 _142064) y t'.
Proof. exact (EQ_MP (@lem8010620 _142062 _142064 y t') (@lem8010617 _142062 _142063 _142064 x y s s' t t' h1 h2)). Qed.
Lemma lem8010624 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8010626 {_142062 _142064 : Type'} (y : cart _142062 _142064) (t' : type24 _142062 _142064) : (term71 _142062 _142064 y t') = (term530 _142062 _142064 y t').
Proof. exact (@lem8010624 (@IN (cart _142062 _142064) y t')). Qed.
Lemma lem8010629 {_142062 _142064 : Type'} (y : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term71 _142062 _142064 y t') : term530 _142062 _142064 y t'.
Proof. exact (EQ_MP (@lem8010626 _142062 _142064 y t') (@lem8010099 _142062 _142064 y t' h1)). Qed.
Lemma lem8010632 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term71 _142062 _142064 y t') (h2 : term170 _142062 _142063 _142064 s s' t t') (h3 : term413 _142062 _142063 _142064 x y s s' t t') : False.
Proof. exact (@lem8010629 _142062 _142064 y t' h1 (@lem8010621 _142062 _142063 _142064 x y s s' t t' h2 h3)). Qed.
Lemma lem8010633 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term71 _142062 _142064 y t') (h2 : term170 _142062 _142063 _142064 s s' t t') (h3 : term413 _142062 _142063 _142064 x y s s' t t') : term531.
Proof. exact (fun h0 : ~ False => @lem8010632 _142062 _142063 _142064 x y s s' t t' h1 h2 h3). Qed.
Lemma lem8010635 (p : Prop) : (term512 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8010636 : term531 = False.
Proof. exact (@lem8010635 False). Qed.
Lemma lem8010637 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term71 _142062 _142064 y t') (h2 : term170 _142062 _142063 _142064 s s' t t') (h3 : term413 _142062 _142063 _142064 x y s s' t t') : False.
Proof. exact (EQ_MP (@lem8010636) (@lem8010633 _142062 _142063 _142064 x y s s' t t' h1 h2 h3)). Qed.
Lemma lem8010638 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term71 _142062 _142064 y t') (h2 : term170 _142062 _142063 _142064 s s' t t') (h3 : term413 _142062 _142063 _142064 x y s s' t t') : (term71 _142062 _142064 y t') = False.
Proof. exact (prop_ext (fun h4 : term71 _142062 _142064 y t' => @lem8010637 _142062 _142063 _142064 x y s s' t t' h1 h2 h3) (fun h4 : False => @lem8010099 _142062 _142064 y t' h1)). Qed.
Lemma lem8010639 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term71 _142062 _142064 y t') (h2 : term170 _142062 _142063 _142064 s s' t t') (h3 : term413 _142062 _142063 _142064 x y s s' t t') : False.
Proof. exact (EQ_MP (@lem8010638 _142062 _142063 _142064 x y s s' t t' h1 h2 h3) (@lem8010099 _142062 _142064 y t' h1)). Qed.
Lemma lem8010640 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term71 _142062 _142063 x s') (h2 : term170 _142062 _142063 _142064 s s' t t') (h3 : term413 _142062 _142063 _142064 x y s s' t t') : (term71 _142062 _142063 x s') = False.
Proof. exact (prop_ext (fun h4 : term71 _142062 _142063 x s' => @lem8010511 _142062 _142063 _142064 x y s s' t t' h1 h2 h3) (fun h4 : False => @lem8010065 _142062 _142063 x s' h1)). Qed.
Lemma lem8010641 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term71 _142062 _142063 x s') (h2 : term170 _142062 _142063 _142064 s s' t t') (h3 : term413 _142062 _142063 _142064 x y s s' t t') : False.
Proof. exact (EQ_MP (@lem8010640 _142062 _142063 _142064 x y s s' t t' h1 h2 h3) (@lem8010065 _142062 _142063 x s' h1)). Qed.
Lemma lem8010642 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term71 _142062 _142064 y t') (h2 : term170 _142062 _142063 _142064 s s' t t') (h3 : term413 _142062 _142063 _142064 x y s s' t t') : (term71 _142062 _142064 y t') = False.
Proof. exact (prop_ext (fun h4 : term71 _142062 _142064 y t' => @lem8010639 _142062 _142063 _142064 x y s s' t t' h1 h2 h3) (fun h4 : False => @lem8009913 _142062 _142064 y t' h1)). Qed.
Lemma lem8010643 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term71 _142062 _142064 y t') (h2 : term170 _142062 _142063 _142064 s s' t t') (h3 : term413 _142062 _142063 _142064 x y s s' t t') : False.
Proof. exact (EQ_MP (@lem8010642 _142062 _142063 _142064 x y s s' t t' h1 h2 h3) (@lem8009913 _142062 _142064 y t' h1)). Qed.
Lemma lem8010644 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term71 _142062 _142063 x s') (h2 : term170 _142062 _142063 _142064 s s' t t') (h3 : term413 _142062 _142063 _142064 x y s s' t t') : (term71 _142062 _142063 x s') = False.
Proof. exact (prop_ext (fun h4 : term71 _142062 _142063 x s' => @lem8010641 _142062 _142063 _142064 x y s s' t t' h1 h2 h3) (fun h4 : False => @lem8009837 _142062 _142063 x s' h1)). Qed.
Lemma lem8010645 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term71 _142062 _142063 x s') (h2 : term170 _142062 _142063 _142064 s s' t t') (h3 : term413 _142062 _142063 _142064 x y s s' t t') : False.
Proof. exact (EQ_MP (@lem8010644 _142062 _142063 _142064 x y s s' t t' h1 h2 h3) (@lem8009837 _142062 _142063 x s' h1)). Qed.
Lemma lem8010646 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term71 _142062 _142064 y t') (h2 : term170 _142062 _142063 _142064 s s' t t') (h3 : term413 _142062 _142063 _142064 x y s s' t t') : (term71 _142062 _142064 y t') = False.
Proof. exact (prop_ext (fun h4 : term71 _142062 _142064 y t' => @lem8010643 _142062 _142063 _142064 x y s s' t t' h1 h2 h3) (fun h4 : False => @lem8009913 _142062 _142064 y t' h1)). Qed.
Lemma lem8010647 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term71 _142062 _142064 y t') (h2 : term170 _142062 _142063 _142064 s s' t t') (h3 : term413 _142062 _142063 _142064 x y s s' t t') : False.
Proof. exact (EQ_MP (@lem8010646 _142062 _142063 _142064 x y s s' t t' h1 h2 h3) (@lem8009913 _142062 _142064 y t' h1)). Qed.
Lemma lem8010648 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term74 _142062 _142064 t) (h2 : term413 _142062 _142063 _142064 x y s s' t t') : (term74 _142062 _142064 t) = False.
Proof. exact (prop_ext (fun h3 : term74 _142062 _142064 t => @lem8010561 _142062 _142063 _142064 x y s s' t t' h1 h2) (fun h3 : False => @lem8009901 _142062 _142064 t h1)). Qed.
Lemma lem8010649 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term74 _142062 _142064 t) (h2 : term413 _142062 _142063 _142064 x y s s' t t') : False.
Proof. exact (EQ_MP (@lem8010648 _142062 _142063 _142064 x y s s' t t' h1 h2) (@lem8009901 _142062 _142064 t h1)). Qed.
Lemma lem8010650 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term74 _142062 _142063 s) (h2 : term413 _142062 _142063 _142064 x y s s' t t') : (term74 _142062 _142063 s) = False.
Proof. exact (prop_ext (fun h3 : term74 _142062 _142063 s => @lem8010536 _142062 _142063 _142064 x y s s' t t' h1 h2) (fun h3 : False => @lem8009882 _142062 _142063 s h1)). Qed.
Lemma lem8010651 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term74 _142062 _142063 s) (h2 : term413 _142062 _142063 _142064 x y s s' t t') : False.
Proof. exact (EQ_MP (@lem8010650 _142062 _142063 _142064 x y s s' t t' h1 h2) (@lem8009882 _142062 _142063 s h1)). Qed.
Lemma lem8010652 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term71 _142062 _142063 x s') (h2 : term170 _142062 _142063 _142064 s s' t t') (h3 : term413 _142062 _142063 _142064 x y s s' t t') : (term71 _142062 _142063 x s') = False.
Proof. exact (prop_ext (fun h4 : term71 _142062 _142063 x s' => @lem8010645 _142062 _142063 _142064 x y s s' t t' h1 h2 h3) (fun h4 : False => @lem8009837 _142062 _142063 x s' h1)). Qed.
Lemma lem8010653 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term71 _142062 _142063 x s') (h2 : term170 _142062 _142063 _142064 s s' t t') (h3 : term413 _142062 _142063 _142064 x y s s' t t') : False.
Proof. exact (EQ_MP (@lem8010652 _142062 _142063 _142064 x y s s' t t' h1 h2 h3) (@lem8009837 _142062 _142063 x s' h1)). Qed.
Lemma lem8010654 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term74 _142062 _142064 t) (h2 : term413 _142062 _142063 _142064 x y s s' t t') : (term74 _142062 _142064 t) = False.
Proof. exact (prop_ext (fun h3 : term74 _142062 _142064 t => @lem8010435 _142062 _142063 _142064 x y s s' t t' h1 h2) (fun h3 : False => @lem8009825 _142062 _142064 t h1)). Qed.
Lemma lem8010655 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term74 _142062 _142064 t) (h2 : term413 _142062 _142063 _142064 x y s s' t t') : False.
Proof. exact (EQ_MP (@lem8010654 _142062 _142063 _142064 x y s s' t t' h1 h2) (@lem8009825 _142062 _142064 t h1)). Qed.
Lemma lem8010656 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term74 _142062 _142063 s) (h2 : term413 _142062 _142063 _142064 x y s s' t t') : (term74 _142062 _142063 s) = False.
Proof. exact (prop_ext (fun h3 : term74 _142062 _142063 s => @lem8010410 _142062 _142063 _142064 x y s s' t t' h1 h2) (fun h3 : False => @lem8009806 _142062 _142063 s h1)). Qed.
Lemma lem8010657 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term74 _142062 _142063 s) (h2 : term413 _142062 _142063 _142064 x y s s' t t') : False.
Proof. exact (EQ_MP (@lem8010656 _142062 _142063 _142064 x y s s' t t' h1 h2) (@lem8009806 _142062 _142063 s h1)). Qed.
Lemma lem8010658 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term71 _142062 _142064 y t') (h2 : term413 _142062 _142063 _142064 x y s s' t t') (h3 : term176 _142062 _142063 _142064 s s' t t') : False.
Proof. exact (or_elim (@lem8009687 _142062 _142063 _142064 s s' t t' h3) (fun h0 : term74 _142062 _142064 t => @lem8010649 _142062 _142063 _142064 x y s s' t t' h0 h2) (fun h0 : term170 _142062 _142063 _142064 s s' t t' => @lem8010647 _142062 _142063 _142064 x y s s' t t' h1 h0 h2)). Qed.
Lemma lem8010659 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term71 _142062 _142064 y t') (h2 : term413 _142062 _142063 _142064 x y s s' t t') : False.
Proof. exact (or_elim (@lem8009672 _142062 _142063 _142064 x y s s' t t' h2) (fun h0 : term74 _142062 _142063 s => @lem8010651 _142062 _142063 _142064 x y s s' t t' h0 h2) (fun h0 : term176 _142062 _142063 _142064 s s' t t' => @lem8010658 _142062 _142063 _142064 x y s s' t t' h1 h2 h0)). Qed.
Lemma lem8010660 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term71 _142062 _142063 x s') (h2 : term413 _142062 _142063 _142064 x y s s' t t') (h3 : term176 _142062 _142063 _142064 s s' t t') : False.
Proof. exact (or_elim (@lem8009681 _142062 _142063 _142064 s s' t t' h3) (fun h0 : term74 _142062 _142064 t => @lem8010655 _142062 _142063 _142064 x y s s' t t' h0 h2) (fun h0 : term170 _142062 _142063 _142064 s s' t t' => @lem8010653 _142062 _142063 _142064 x y s s' t t' h1 h0 h2)). Qed.
Lemma lem8010661 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term71 _142062 _142063 x s') (h2 : term413 _142062 _142063 _142064 x y s s' t t') : False.
Proof. exact (or_elim (@lem8009672 _142062 _142063 _142064 x y s s' t t' h2) (fun h0 : term74 _142062 _142063 s => @lem8010657 _142062 _142063 _142064 x y s s' t t' h0 h2) (fun h0 : term176 _142062 _142063 _142064 s s' t t' => @lem8010660 _142062 _142063 _142064 x y s s' t t' h1 h2 h0)). Qed.
Lemma lem8010662 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term413 _142062 _142063 _142064 x y s s' t t') : False.
Proof. exact (or_elim (@lem8009674 _142062 _142063 _142064 x y s s' t t' h1) (fun h0 : term71 _142062 _142063 x s' => @lem8010661 _142062 _142063 _142064 x y s s' t t' h0 h1) (fun h0 : term71 _142062 _142064 y t' => @lem8010659 _142062 _142063 _142064 x y s s' t t' h0 h1)). Qed.
Lemma lem8010663 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (x' : cart _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (x'' : cart _142062 _142064) (t' : type24 _142062 _142064) (h1 : term376 _142062 _142063 _142064 x y s x' s' t x'' t') : False.
Proof. exact (or_elim (@lem8009664 _142062 _142063 _142064 x y s x' s' t x'' t' h1) (fun h0 : term153 _142062 _142063 s x' s' => @lem8010248 _142062 _142063 _142064 x y t x'' t' s x' s' h1 h0) (fun h0 : term153 _142062 _142064 t x'' t' => @lem8010385 _142062 _142063 _142064 x y s x' s' t x'' t' h1 h0)). Qed.
Lemma lem8010664 {_142062 _142063 _142064 : Type'} (x' : cart _142062 _142063) (x'' : cart _142062 _142064) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term489 _142062 _142063 _142064 x' x'' x y s s' t t') : False.
Proof. exact (or_elim (@lem8009657 _142062 _142063 _142064 x' x'' x y s s' t t' h1) (fun h0 : term376 _142062 _142063 _142064 x y s x' s' t x'' t' => @lem8010663 _142062 _142063 _142064 x y s x' s' t x'' t' h0) (fun h0 : term413 _142062 _142063 _142064 x y s s' t t' => @lem8010662 _142062 _142063 _142064 x y s s' t t' h0)). Qed.
Lemma lem8010665 {_142062 _142063 _142064 : Type'} (x' : cart _142062 _142063) (x'' : cart _142062 _142064) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term489 _142062 _142063 _142064 x' x'' x y s s' t t') : (term489 _142062 _142063 _142064 x' x'' x y s s' t t') = False.
Proof. exact (prop_ext (fun h2 : term489 _142062 _142063 _142064 x' x'' x y s s' t t' => @lem8010664 _142062 _142063 _142064 x' x'' x y s s' t t' h1) (fun h2 : False => @lem8009657 _142062 _142063 _142064 x' x'' x y s s' t t' h1)). Qed.
Lemma lem8010666 {_142062 _142063 _142064 : Type'} (x' : cart _142062 _142063) (x'' : cart _142062 _142064) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term489 _142062 _142063 _142064 x' x'' x y s s' t t') : False.
Proof. exact (EQ_MP (@lem8010665 _142062 _142063 _142064 x' x'' x y s s' t t' h1) (@lem8009657 _142062 _142063 _142064 x' x'' x y s s' t t' h1)). Qed.
Lemma lem8010667 {_142062 _142063 _142064 : Type'} (x' : cart _142062 _142063) (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term492 _142062 _142063 _142064 x' x y s s' t t') : False.
Proof. exact (ex_elim (@lem8009460 _142062 _142063 _142064 x' x y s s' t t' h1) (fun x'' : cart _142062 _142064 => fun h0 : term491 _142062 _142063 _142064 x' x y s s' t t' x'' => @lem8010666 _142062 _142063 _142064 x' x'' x y s s' t t' h0)). Qed.
Lemma lem8010668 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (y : cart _142062 _142064) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term494 _142062 _142063 _142064 x y s s' t t') : False.
Proof. exact (ex_elim (@lem8009459 _142062 _142063 _142064 x y s s' t t' h1) (fun x' : cart _142062 _142063 => fun h0 : term493 _142062 _142063 _142064 x y s s' t t' x' => @lem8010667 _142062 _142063 _142064 x' x y s s' t t' h0)). Qed.
Lemma lem8010669 {_142062 _142063 _142064 : Type'} (x : cart _142062 _142063) (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term496 _142062 _142063 _142064 x s s' t t') : False.
Proof. exact (ex_elim (@lem8009458 _142062 _142063 _142064 x s s' t t' h1) (fun y : cart _142062 _142064 => fun h0 : term495 _142062 _142063 _142064 x s s' t t' y => @lem8010668 _142062 _142063 _142064 x y s s' t t' h0)). Qed.
Lemma lem8010670 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term113 _142062 _142063 _142064 s s' t t') : False.
Proof. exact (ex_elim (@lem8009457 _142062 _142063 _142064 s s' t t' h1) (fun x : cart _142062 _142063 => fun h0 : term497 _142062 _142063 _142064 s s' t t' x => @lem8010669 _142062 _142063 _142064 x s s' t t' h0)). Qed.
Lemma lem8010671 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term113 _142062 _142063 _142064 s s' t t') : (term113 _142062 _142063 _142064 s s' t t') = False.
Proof. exact (prop_ext (fun h2 : term113 _142062 _142063 _142064 s s' t t' => @lem8010670 _142062 _142063 _142064 s s' t t' h1) (fun h2 : False => @lem8008455 _142062 _142063 _142064 s s' t t' h1)). Qed.
Lemma lem8010672 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) (h1 : term113 _142062 _142063 _142064 s s' t t') : False.
Proof. exact (EQ_MP (@lem8010671 _142062 _142063 _142064 s s' t t' h1) (@lem8008455 _142062 _142063 _142064 s s' t t' h1)). Qed.
Lemma lem8010673 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : term112 _142062 _142063 _142064 s s' t t'.
Proof. exact (fun h0 : term113 _142062 _142063 _142064 s s' t t' => @lem8010672 _142062 _142063 _142064 s s' t t' h0). Qed.
Lemma lem8010674 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) (t' : type24 _142062 _142064) : (term65 _142062 _142063 _142064 s t s' t') = (term85 _142062 _142063 _142064 s s' t t').
Proof. exact (EQ_MP (@lem8008454 _142062 _142063 _142064 s s' t t') (@lem8010673 _142062 _142063 _142064 s s' t t')). Qed.
Lemma lem8010679 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (s' : type24 _142062 _142063) (t : type24 _142062 _142064) : term89 _142062 _142063 _142064 s s' t.
Proof. exact (fun t' : type24 _142062 _142064 => @lem8010674 _142062 _142063 _142064 s s' t t'). Qed.
Lemma lem8010684 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) (t : type24 _142062 _142064) : term93 _142062 _142063 _142064 s t.
Proof. exact (fun s' : type24 _142062 _142063 => @lem8010679 _142062 _142063 _142064 s s' t). Qed.
Lemma lem8010689 {_142062 _142063 _142064 : Type'} (s : type24 _142062 _142063) : term97 _142062 _142063 _142064 s.
Proof. exact (fun t : type24 _142062 _142064 => @lem8010684 _142062 _142063 _142064 s t). Qed.
Lemma lem8010694 {_142062 _142063 _142064 : Type'} : term101 _142062 _142063 _142064.
Proof. exact (fun s : type24 _142062 _142063 => @lem8010689 _142062 _142063 _142064 s). Qed.
Lemma lem8010695 {_142062 _142063 _142064 : Type'} : term103 _142062 _142063 _142064.
Proof. exact (EQ_MP (@lem8008450 _142062 _142063 _142064) (@lem8010694 _142062 _142063 _142064)). Qed.
Lemma lem8010697 {_142062 _142063 _142064 : Type'} : term103 _142062 _142063 _142064.
Proof. exact (@lem8008232 _142062 _142063 _142064 (@lem8010695 _142062 _142063 _142064)). Qed.
Lemma lem8010698 {_142062 _142063 _142064 : Type'} (h1 : term104 _142062 _142063 _142064) : False.
Proof. exact (@lem8010697 _142062 _142063 _142064 (@lem8008216 _142062 _142063 _142064 h1)). Qed.
Lemma lem8010699 {_142062 _142063 _142064 : Type'} (h1 : term104 _142062 _142063 _142064) : (term104 _142062 _142063 _142064) = False.
Proof. exact (prop_ext (fun h2 : term104 _142062 _142063 _142064 => @lem8010698 _142062 _142063 _142064 h1) (fun h2 : False => @lem8008216 _142062 _142063 _142064 h1)). Qed.
Lemma lem8010700 {_142062 _142063 _142064 : Type'} (h1 : term104 _142062 _142063 _142064) : False.
Proof. exact (EQ_MP (@lem8010699 _142062 _142063 _142064 h1) (@lem8008216 _142062 _142063 _142064 h1)). Qed.
Lemma lem8010701 {_142062 _142063 _142064 : Type'} : term103 _142062 _142063 _142064.
Proof. exact (fun h0 : term104 _142062 _142063 _142064 => @lem8010700 _142062 _142063 _142064 h0). Qed.
Lemma lem8010702 {_142062 _142063 _142064 : Type'} : term101 _142062 _142063 _142064.
Proof. exact (EQ_MP (@lem8008215 _142062 _142063 _142064) (@lem8010701 _142062 _142063 _142064)). Qed.
Lemma lem8010703 {_142062 _142063 _142064 : Type'} : term100 _142062 _142063 _142064.
Proof. exact (EQ_MP (@lem8008211 _142062 _142063 _142064) (@lem8010702 _142062 _142063 _142064)). Qed.
