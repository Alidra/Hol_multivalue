Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4211_term_abbrevs.
Require Import thm32_spec.
Require Import thm37_spec.
Require Import thm43_spec.
Lemma lem2593 (p : Prop) (p' : Prop) (h1 : p = p') : p = p'.
Proof. exact (h1). Qed.
Lemma lem2594 (p' : Prop) (q : Prop) (q' : Prop) (h1 : term0 p' q q') : term0 p' q q'.
Proof. exact (h1). Qed.
Lemma lem2595 (p : Prop) (q : Prop) (h1 : p -> q) : p -> q.
Proof. exact (h1). Qed.
Lemma lem2596 (p' : Prop) (h1 : p') : p'.
Proof. exact (h1). Qed.
Lemma lem2597 (p' : Prop) (p : Prop) : term1 p' p.
Proof. exact (@lem43 p' p). Qed.
Lemma lem2599 (p : Prop) (p' : Prop) : term2 p p'.
Proof. exact (@lem37 p p'). Qed.
Lemma lem2602 (p : Prop) (p' : Prop) (h1 : p = p') : p' -> p.
Proof. exact (@lem2597 p' p (@lem2593 p p' h1)). Qed.
Lemma lem2603 (p : Prop) (p' : Prop) (h1 : p = p') : p -> p'.
Proof. exact (@lem2599 p p' (@lem2593 p p' h1)). Qed.
Lemma lem2604 (p' : Prop) (p : Prop) (h1 : p' -> p) : p' -> p.
Proof. exact (h1). Qed.
Lemma lem2605 (p : Prop) (p' : Prop) (h1 : p -> p') : p -> p'.
Proof. exact (h1). Qed.
Lemma lem3216 (p : Prop) (h1 : p) : p.
Proof. exact (h1). Qed.
Lemma lem3217 (p : Prop) (q : Prop) (h1 : p) (h2 : p -> q) : q.
Proof. exact (@lem2595 p q h2 (@lem3216 p h1)). Qed.
Lemma lem3218 (p : Prop) (h1 : p) : p.
Proof. exact (h1). Qed.
Lemma lem3219 (p : Prop) (p' : Prop) (h1 : p) (h2 : p -> p') : p'.
Proof. exact (@lem2605 p p' h2 (@lem3218 p h1)). Qed.
Lemma lem3230 (p' : Prop) (h1 : p') : p'.
Proof. exact (h1). Qed.
Lemma lem3231 (p' : Prop) (p : Prop) (h1 : p') (h2 : p' -> p) : p.
Proof. exact (@lem2604 p' p h2 (@lem3230 p' h1)). Qed.
Lemma lem3232 (p' : Prop) (p : Prop) (h1 : p') (h2 : p' -> p) : p' = p.
Proof. exact (prop_ext (fun h3 : p' => @lem3231 p' p h1 h2) (fun h3 : p => @lem2596 p' h1)). Qed.
Lemma lem3233 (p' : Prop) (p : Prop) (h1 : p') (h2 : p' -> p) : p.
Proof. exact (EQ_MP (@lem3232 p' p h1 h2) (@lem2596 p' h1)). Qed.
Lemma lem3244 (p' : Prop) (h1 : p') : p'.
Proof. exact (h1). Qed.
Lemma lem3245 (p' : Prop) (p : Prop) (h1 : p') (h2 : p' -> p) : p.
Proof. exact (@lem2604 p' p h2 (@lem3244 p' h1)). Qed.
Lemma lem3246 (p' : Prop) (p : Prop) (h1 : p -> p') (h2 : p' -> p) : p' = p.
Proof. exact (prop_ext (fun h3 : p' => @lem3245 p' p h3 h2) (fun h3 : p => @lem3219 p p' h3 h1)). Qed.
Lemma lem3247 (p' : Prop) (p : Prop) (h1 : p) (h2 : p -> p') (h3 : p' -> p) : p.
Proof. exact (EQ_MP (@lem3246 p' p h2 h3) (@lem3219 p p' h1 h2)). Qed.
Lemma lem3248 (p' : Prop) (p : Prop) (h1 : p') (h2 : p -> p') (h3 : p' -> p) : p = p.
Proof. exact (prop_ext (fun h4 : p => @lem3247 p' p h4 h2 h3) (fun h4 : p => @lem3233 p' p h1 h3)). Qed.
Lemma lem3249 (p' : Prop) (p : Prop) (h1 : p') (h2 : p -> p') (h3 : p' -> p) : p.
Proof. exact (EQ_MP (@lem3248 p' p h1 h2 h3) (@lem3233 p' p h1 h3)). Qed.
Lemma lem3443 (p' : Prop) (h1 : p') : p'.
Proof. exact (h1). Qed.
Lemma lem3444 (p' : Prop) (q : Prop) (q' : Prop) (h1 : p') (h2 : term0 p' q q') : q = q'.
Proof. exact (@lem2594 p' q q' h2 (@lem3443 p' h1)). Qed.
Lemma lem3445 (q' : Prop) (q : Prop) : term1 q' q.
Proof. exact (@lem43 q' q). Qed.
Lemma lem3447 (q : Prop) (q' : Prop) : term2 q q'.
Proof. exact (@lem37 q q'). Qed.
Lemma lem3450 (p' : Prop) (q : Prop) (q' : Prop) (h1 : p') (h2 : term0 p' q q') : q' -> q.
Proof. exact (@lem3445 q' q (@lem3444 p' q q' h1 h2)). Qed.
Lemma lem3451 (p' : Prop) (q : Prop) (q' : Prop) (h1 : p') (h2 : term0 p' q q') : q -> q'.
Proof. exact (@lem3447 q q' (@lem3444 p' q q' h1 h2)). Qed.
Lemma lem3453 (q : Prop) (q' : Prop) (h1 : q -> q') : q -> q'.
Proof. exact (h1). Qed.
Lemma lem3454 (q : Prop) (h1 : q) : q.
Proof. exact (h1). Qed.
Lemma lem3455 (q : Prop) (q' : Prop) (h1 : q) (h2 : q -> q') : q'.
Proof. exact (@lem3453 q q' h2 (@lem3454 q h1)). Qed.
Lemma lem3456 (p : Prop) (q : Prop) (q' : Prop) (h1 : p) (h2 : p -> q) (h3 : q -> q') : q = q'.
Proof. exact (prop_ext (fun h4 : q => @lem3455 q q' h4 h3) (fun h4 : q' => @lem3217 p q h1 h2)). Qed.
Lemma lem3457 (p : Prop) (q : Prop) (q' : Prop) (h1 : p) (h2 : p -> q) (h3 : q -> q') : q'.
Proof. exact (EQ_MP (@lem3456 p q q' h1 h2 h3) (@lem3217 p q h1 h2)). Qed.
Lemma lem3458 (q' : Prop) (p : Prop) (q : Prop) (h1 : p) (h2 : p -> q) : term3 q q'.
Proof. exact (fun h0 : q -> q' => @lem3457 p q q' h1 h2 h0). Qed.
Lemma lem3459 (q' : Prop) (p : Prop) (q : Prop) (h1 : p) (h2 : p -> q) : term4 q q'.
Proof. exact (fun h0 : q' -> q => @lem3458 q' p q h1 h2). Qed.
Lemma lem3460 (p : Prop) (p' : Prop) (q : Prop) (q' : Prop) (h1 : p) (h2 : p') (h3 : p -> q) (h4 : term0 p' q q') : term3 q q'.
Proof. exact (@lem3459 q' p q h1 h3 (@lem3450 p' q q' h2 h4)). Qed.
Lemma lem3461 (p : Prop) (p' : Prop) (q : Prop) (q' : Prop) (h1 : p) (h2 : p') (h3 : p -> q) (h4 : term0 p' q q') : q'.
Proof. exact (@lem3460 p p' q q' h1 h2 h3 h4 (@lem3451 p' q q' h2 h4)). Qed.
Lemma lem3462 (p : Prop) (p' : Prop) (q : Prop) (q' : Prop) (h1 : p) (h2 : p') (h3 : p -> q) (h4 : term0 p' q q') : p' = q'.
Proof. exact (prop_ext (fun h5 : p' => @lem3461 p p' q q' h1 h2 h3 h4) (fun h5 : q' => @lem2596 p' h2)). Qed.
Lemma lem3463 (p : Prop) (p' : Prop) (q : Prop) (q' : Prop) (h1 : p) (h2 : p') (h3 : p -> q) (h4 : term0 p' q q') : q'.
Proof. exact (EQ_MP (@lem3462 p p' q q' h1 h2 h3 h4) (@lem2596 p' h2)). Qed.
Lemma lem3464 (p : Prop) (p' : Prop) (q : Prop) (q' : Prop) (h1 : p') (h2 : p -> p') (h3 : p -> q) (h4 : p' -> p) (h5 : term0 p' q q') : p = q'.
Proof. exact (prop_ext (fun h6 : p => @lem3463 p p' q q' h6 h1 h3 h5) (fun h6 : q' => @lem3249 p' p h1 h2 h4)). Qed.
Lemma lem3465 (p : Prop) (p' : Prop) (q : Prop) (q' : Prop) (h1 : p') (h2 : p -> p') (h3 : p -> q) (h4 : p' -> p) (h5 : term0 p' q q') : q'.
Proof. exact (EQ_MP (@lem3464 p p' q q' h1 h2 h3 h4 h5) (@lem3249 p' p h1 h2 h4)). Qed.
Lemma lem3466 (p : Prop) (p' : Prop) (q : Prop) (q' : Prop) (h1 : p') (h2 : p -> q) (h3 : p' -> p) (h4 : term0 p' q q') : term5 p p' q'.
Proof. exact (fun h0 : p -> p' => @lem3465 p p' q q' h1 h0 h2 h3 h4). Qed.
Lemma lem3467 (p : Prop) (p' : Prop) (q : Prop) (q' : Prop) (h1 : p') (h2 : p -> q) (h3 : term0 p' q q') : term6 p p' q'.
Proof. exact (fun h0 : p' -> p => @lem3466 p p' q q' h1 h2 h0 h3). Qed.
Lemma lem3468 (p : Prop) (p' : Prop) (q : Prop) (q' : Prop) (h1 : p') (h2 : p = p') (h3 : p -> q) (h4 : term0 p' q q') : term5 p p' q'.
Proof. exact (@lem3467 p p' q q' h1 h3 h4 (@lem2602 p p' h2)). Qed.
Lemma lem3469 (p : Prop) (p' : Prop) (q : Prop) (q' : Prop) (h1 : p') (h2 : p = p') (h3 : p -> q) (h4 : term0 p' q q') : q'.
Proof. exact (@lem3468 p p' q q' h1 h2 h3 h4 (@lem2603 p p' h2)). Qed.
Lemma lem3470 (p : Prop) (p' : Prop) (q : Prop) (q' : Prop) (h1 : p = p') (h2 : p -> q) (h3 : term0 p' q q') : p' -> q'.
Proof. exact (fun h0 : p' => @lem3469 p p' q q' h0 h1 h2 h3). Qed.
Lemma lem3471 (p : Prop) (p' : Prop) (q : Prop) (q' : Prop) (h1 : p = p') (h2 : term0 p' q q') : term7 p q p' q'.
Proof. exact (fun h0 : p -> q => @lem3470 p p' q q' h1 h0 h2). Qed.
Lemma lem3472 (p' : Prop) (q' : Prop) (h1 : p' -> q') : p' -> q'.
Proof. exact (h1). Qed.
Lemma lem3473 (p : Prop) (h1 : p) : p.
Proof. exact (h1). Qed.
Lemma lem3474 (p' : Prop) (p : Prop) : term1 p' p.
Proof. exact (@lem43 p' p). Qed.
Lemma lem3476 (p : Prop) (p' : Prop) : term2 p p'.
Proof. exact (@lem37 p p'). Qed.
Lemma lem3479 (p : Prop) (p' : Prop) (h1 : p = p') : p' -> p.
Proof. exact (@lem3474 p' p (@lem2593 p p' h1)). Qed.
Lemma lem3480 (p : Prop) (p' : Prop) (h1 : p = p') : p -> p'.
Proof. exact (@lem3476 p p' (@lem2593 p p' h1)). Qed.
Lemma lem3482 (p : Prop) (p' : Prop) (h1 : p -> p') : p -> p'.
Proof. exact (h1). Qed.
Lemma lem4010 (p' : Prop) (h1 : p') : p'.
Proof. exact (h1). Qed.
Lemma lem4011 (p' : Prop) (q' : Prop) (h1 : p') (h2 : p' -> q') : q'.
Proof. exact (@lem3472 p' q' h2 (@lem4010 p' h1)). Qed.
Lemma lem4163 (p' : Prop) (h1 : p') : p'.
Proof. exact (h1). Qed.
Lemma lem4164 (p' : Prop) (q : Prop) (q' : Prop) (h1 : p') (h2 : term0 p' q q') : q = q'.
Proof. exact (@lem2594 p' q q' h2 (@lem4163 p' h1)). Qed.
Lemma lem4165 (p : Prop) (h1 : p) : p.
Proof. exact (h1). Qed.
Lemma lem4166 (p : Prop) (p' : Prop) (h1 : p) (h2 : p -> p') : p'.
Proof. exact (@lem3482 p p' h2 (@lem4165 p h1)). Qed.
Lemma lem4167 (p : Prop) (p' : Prop) (h1 : p) (h2 : p -> p') : p = p'.
Proof. exact (prop_ext (fun h3 : p => @lem4166 p p' h1 h2) (fun h3 : p' => @lem3473 p h1)). Qed.
Lemma lem4168 (p : Prop) (p' : Prop) (h1 : p) (h2 : p -> p') : p'.
Proof. exact (EQ_MP (@lem4167 p p' h1 h2) (@lem3473 p h1)). Qed.
Lemma lem4169 (q' : Prop) (q : Prop) : term1 q' q.
Proof. exact (@lem43 q' q). Qed.
Lemma lem4171 (q : Prop) (q' : Prop) : term2 q q'.
Proof. exact (@lem37 q q'). Qed.
Lemma lem4174 (p' : Prop) (q : Prop) (q' : Prop) (h1 : p') (h2 : term0 p' q q') : q' -> q.
Proof. exact (@lem4169 q' q (@lem4164 p' q q' h1 h2)). Qed.
Lemma lem4175 (p' : Prop) (q : Prop) (q' : Prop) (h1 : p') (h2 : term0 p' q q') : q -> q'.
Proof. exact (@lem4171 q q' (@lem4164 p' q q' h1 h2)). Qed.
Lemma lem4176 (q' : Prop) (q : Prop) (h1 : q' -> q) : q' -> q.
Proof. exact (h1). Qed.
Lemma lem4192 (q' : Prop) (h1 : q') : q'.
Proof. exact (h1). Qed.
Lemma lem4193 (q' : Prop) (q : Prop) (h1 : q') (h2 : q' -> q) : q.
Proof. exact (@lem4176 q' q h2 (@lem4192 q' h1)). Qed.
Lemma lem4194 (p' : Prop) (q' : Prop) (q : Prop) (h1 : p') (h2 : p' -> q') (h3 : q' -> q) : q' = q.
Proof. exact (prop_ext (fun h4 : q' => @lem4193 q' q h4 h3) (fun h4 : q => @lem4011 p' q' h1 h2)). Qed.
Lemma lem4195 (p' : Prop) (q' : Prop) (q : Prop) (h1 : p') (h2 : p' -> q') (h3 : q' -> q) : q.
Proof. exact (EQ_MP (@lem4194 p' q' q h1 h2 h3) (@lem4011 p' q' h1 h2)). Qed.
Lemma lem4196 (p' : Prop) (q' : Prop) (q : Prop) (h1 : p') (h2 : p' -> q') (h3 : q' -> q) : term8 q' q.
Proof. exact (fun h0 : q -> q' => @lem4195 p' q' q h1 h2 h3). Qed.
Lemma lem4197 (q : Prop) (p' : Prop) (q' : Prop) (h1 : p') (h2 : p' -> q') : term9 q' q.
Proof. exact (fun h0 : q' -> q => @lem4196 p' q' q h1 h2 h0). Qed.
Lemma lem4198 (p' : Prop) (q : Prop) (q' : Prop) (h1 : p') (h2 : p' -> q') (h3 : term0 p' q q') : term8 q' q.
Proof. exact (@lem4197 q p' q' h1 h2 (@lem4174 p' q q' h1 h3)). Qed.
Lemma lem4199 (p' : Prop) (q : Prop) (q' : Prop) (h1 : p') (h2 : p' -> q') (h3 : term0 p' q q') : q.
Proof. exact (@lem4198 p' q q' h1 h2 h3 (@lem4175 p' q q' h1 h3)). Qed.
Lemma lem4200 (p : Prop) (p' : Prop) (q : Prop) (q' : Prop) (h1 : p) (h2 : p -> p') (h3 : p' -> q') (h4 : term0 p' q q') : p' = q.
Proof. exact (prop_ext (fun h5 : p' => @lem4199 p' q q' h5 h3 h4) (fun h5 : q => @lem4168 p p' h1 h2)). Qed.
Lemma lem4201 (p : Prop) (p' : Prop) (q : Prop) (q' : Prop) (h1 : p) (h2 : p -> p') (h3 : p' -> q') (h4 : term0 p' q q') : q.
Proof. exact (EQ_MP (@lem4200 p p' q q' h1 h2 h3 h4) (@lem4168 p p' h1 h2)). Qed.
Lemma lem4202 (p : Prop) (p' : Prop) (q : Prop) (q' : Prop) (h1 : p) (h2 : p' -> q') (h3 : term0 p' q q') : term5 p p' q.
Proof. exact (fun h0 : p -> p' => @lem4201 p p' q q' h1 h0 h2 h3). Qed.
Lemma lem4203 (p : Prop) (p' : Prop) (q : Prop) (q' : Prop) (h1 : p) (h2 : p' -> q') (h3 : term0 p' q q') : term6 p p' q.
Proof. exact (fun h0 : p' -> p => @lem4202 p p' q q' h1 h2 h3). Qed.
Lemma lem4204 (p : Prop) (p' : Prop) (q : Prop) (q' : Prop) (h1 : p) (h2 : p = p') (h3 : p' -> q') (h4 : term0 p' q q') : term5 p p' q.
Proof. exact (@lem4203 p p' q q' h1 h3 h4 (@lem3479 p p' h2)). Qed.
Lemma lem4205 (p : Prop) (p' : Prop) (q : Prop) (q' : Prop) (h1 : p) (h2 : p = p') (h3 : p' -> q') (h4 : term0 p' q q') : q.
Proof. exact (@lem4204 p p' q q' h1 h2 h3 h4 (@lem3480 p p' h2)). Qed.
Lemma lem4206 (p : Prop) (p' : Prop) (q : Prop) (q' : Prop) (h1 : p = p') (h2 : p' -> q') (h3 : term0 p' q q') : p -> q.
Proof. exact (fun h0 : p => @lem4205 p p' q q' h0 h1 h2 h3). Qed.
Lemma lem4207 (p : Prop) (p' : Prop) (q : Prop) (q' : Prop) (h1 : p = p') (h2 : term0 p' q q') : term7 p' q' p q.
Proof. exact (fun h0 : p' -> q' => @lem4206 p p' q q' h1 h0 h2). Qed.
Lemma lem4208 (p : Prop) (p' : Prop) (q : Prop) (q' : Prop) (h1 : p = p') (h2 : term0 p' q q') : term10 p' q' p q.
Proof. exact (conj (@lem3471 p p' q q' h1 h2) (@lem4207 p p' q q' h1 h2)). Qed.
Lemma lem4209 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : (term10 p' q' p q) = ((p -> q) = (p' -> q')).
Proof. exact (@lem32 (p -> q) (p' -> q')). Qed.
Lemma lem4210 (p : Prop) (p' : Prop) (q : Prop) (q' : Prop) (h1 : p = p') (h2 : term0 p' q q') : (p -> q) = (p' -> q').
Proof. exact (EQ_MP (@lem4209 p q p' q') (@lem4208 p p' q q' h1 h2)). Qed.
Lemma lem4211 (q : Prop) (q' : Prop) (p : Prop) (p' : Prop) (h1 : p = p') : term11 p q p' q'.
Proof. exact (fun h0 : term0 p' q q' => @lem4210 p p' q q' h1 h0). Qed.
