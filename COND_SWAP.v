Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import COND_SWAP_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem13157 (p : Prop) : term0 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem13158 (p : Prop) : (term0 p) = (term1 p).
Proof. exact (eq_refl (term0 p)). Qed.
Lemma lem13159 (p : Prop) : term1 p.
Proof. exact (EQ_MP (@lem13158 p) (@lem13157 p)). Qed.
Lemma lem13160 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem13161 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem13162 {A : Type'} (y : A) (x : A) : (term2 A y x) = (term2 A y x).
Proof. exact (eq_refl (term2 A y x)). Qed.
Lemma lem13163 {A : Type'} (y : A) (x : A) (p : Prop) (h1 : p = True) : (term3 A y x p) = (term4 A y x).
Proof. exact (MK_COMB (@lem13162 A y x) (@lem13160 p h1)). Qed.
Lemma lem13164 {A : Type'} (y : A) (x : A) : (term4 A y x) = ((term5 A x y) = (@COND A True y x)).
Proof. exact (eq_refl (term4 A y x)). Qed.
Lemma lem13165 {A : Type'} (y : A) (x : A) (p : Prop) : (term6 A y x p) = (term6 A y x p).
Proof. exact (eq_refl (term6 A y x p)). Qed.
Lemma lem13166 {A : Type'} (p : Prop) (y : A) (x : A) : ((term3 A y x p) = (term4 A y x)) = ((term3 A y x p) = ((term5 A x y) = (@COND A True y x))).
Proof. exact (MK_COMB (@lem13165 A y x p) (@lem13164 A y x)). Qed.
Lemma lem13167 {A : Type'} (p : Prop) (y : A) (x : A) : (term3 A y x p) = ((term7 A p x y) = (@COND A p y x)).
Proof. exact (eq_refl (term3 A y x p)). Qed.
Lemma lem13168 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem13169 {A : Type'} (p : Prop) (y : A) (x : A) : (term6 A y x p) = (term8 A p y x).
Proof. exact (MK_COMB (@lem13168) (@lem13167 A p y x)). Qed.
Lemma lem13170 {A : Type'} (y : A) (x : A) : ((term5 A x y) = (@COND A True y x)) = ((term5 A x y) = (@COND A True y x)).
Proof. exact (eq_refl ((term5 A x y) = (@COND A True y x))). Qed.
Lemma lem13171 {A : Type'} (p : Prop) (y : A) (x : A) : ((term3 A y x p) = ((term5 A x y) = (@COND A True y x))) = (((term7 A p x y) = (@COND A p y x)) = ((term5 A x y) = (@COND A True y x))).
Proof. exact (MK_COMB (@lem13169 A p y x) (@lem13170 A y x)). Qed.
Lemma lem13172 {A : Type'} (p : Prop) (y : A) (x : A) : ((term3 A y x p) = (term4 A y x)) = (((term7 A p x y) = (@COND A p y x)) = ((term5 A x y) = (@COND A True y x))).
Proof. exact (TRANS (@lem13166 A p y x) (@lem13171 A p y x)). Qed.
Lemma lem13173 {A : Type'} (y : A) (x : A) (p : Prop) (h1 : p = True) : ((term7 A p x y) = (@COND A p y x)) = ((term5 A x y) = (@COND A True y x)).
Proof. exact (EQ_MP (@lem13172 A p y x) (@lem13163 A y x p h1)). Qed.
Lemma lem13174 {A : Type'} (y : A) (x : A) (p : Prop) (h1 : p = True) : ((term5 A x y) = (@COND A True y x)) = ((term7 A p x y) = (@COND A p y x)).
Proof. exact (SYM (@lem13173 A y x p h1)). Qed.
Lemma lem13175 {A : Type'} (y : A) (x : A) : (term2 A y x) = (term2 A y x).
Proof. exact (eq_refl (term2 A y x)). Qed.
Lemma lem13176 {A : Type'} (y : A) (x : A) (p : Prop) (h1 : p = False) : (term3 A y x p) = (term9 A y x).
Proof. exact (MK_COMB (@lem13175 A y x) (@lem13161 p h1)). Qed.
Lemma lem13177 {A : Type'} (y : A) (x : A) : (term9 A y x) = ((term10 A x y) = (@COND A False y x)).
Proof. exact (eq_refl (term9 A y x)). Qed.
Lemma lem13178 {A : Type'} (y : A) (x : A) (p : Prop) : (term6 A y x p) = (term6 A y x p).
Proof. exact (eq_refl (term6 A y x p)). Qed.
Lemma lem13179 {A : Type'} (p : Prop) (y : A) (x : A) : ((term3 A y x p) = (term9 A y x)) = ((term3 A y x p) = ((term10 A x y) = (@COND A False y x))).
Proof. exact (MK_COMB (@lem13178 A y x p) (@lem13177 A y x)). Qed.
Lemma lem13180 {A : Type'} (p : Prop) (y : A) (x : A) : (term3 A y x p) = ((term7 A p x y) = (@COND A p y x)).
Proof. exact (eq_refl (term3 A y x p)). Qed.
Lemma lem13181 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem13182 {A : Type'} (p : Prop) (y : A) (x : A) : (term6 A y x p) = (term8 A p y x).
Proof. exact (MK_COMB (@lem13181) (@lem13180 A p y x)). Qed.
Lemma lem13183 {A : Type'} (y : A) (x : A) : ((term10 A x y) = (@COND A False y x)) = ((term10 A x y) = (@COND A False y x)).
Proof. exact (eq_refl ((term10 A x y) = (@COND A False y x))). Qed.
Lemma lem13184 {A : Type'} (p : Prop) (y : A) (x : A) : ((term3 A y x p) = ((term10 A x y) = (@COND A False y x))) = (((term7 A p x y) = (@COND A p y x)) = ((term10 A x y) = (@COND A False y x))).
Proof. exact (MK_COMB (@lem13182 A p y x) (@lem13183 A y x)). Qed.
Lemma lem13185 {A : Type'} (p : Prop) (y : A) (x : A) : ((term3 A y x p) = (term9 A y x)) = (((term7 A p x y) = (@COND A p y x)) = ((term10 A x y) = (@COND A False y x))).
Proof. exact (TRANS (@lem13179 A p y x) (@lem13184 A p y x)). Qed.
Lemma lem13186 {A : Type'} (y : A) (x : A) (p : Prop) (h1 : p = False) : ((term7 A p x y) = (@COND A p y x)) = ((term10 A x y) = (@COND A False y x)).
Proof. exact (EQ_MP (@lem13185 A p y x) (@lem13176 A y x p h1)). Qed.
Lemma lem13187 {A : Type'} (y : A) (x : A) (p : Prop) (h1 : p = False) : ((term10 A x y) = (@COND A False y x)) = ((term7 A p x y) = (@COND A p y x)).
Proof. exact (SYM (@lem13186 A y x p h1)). Qed.
Lemma lem13191 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem13192 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem13193 {A : Type'} : (term11 A) = (@COND A False).
Proof. exact (MK_COMB (@lem13192 A) (@lem13191)). Qed.
Lemma lem13194 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem13195 {A : Type'} (x : A) : (term12 A x) = (@COND A False x).
Proof. exact (MK_COMB (@lem13193 A) (@lem13194 A x)). Qed.
Lemma lem13196 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem13197 {A : Type'} (x : A) (y : A) : (term5 A x y) = (@COND A False x y).
Proof. exact (MK_COMB (@lem13195 A x) (@lem13196 A y)). Qed.
Lemma lem13199 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem13200 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem13199 A t1 t2). Qed.
Lemma lem13201 {A : Type'} (x : A) (y : A) : (@COND A False x y) = y.
Proof. exact (@lem13200 A x y). Qed.
Lemma lem13202 {A : Type'} (x : A) (y : A) : (term5 A x y) = y.
Proof. exact (TRANS (@lem13197 A x y) (@lem13201 A x y)). Qed.
Lemma lem13203 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem13204 {A : Type'} (x : A) (y : A) : (term13 A x y) = (@eq A y).
Proof. exact (MK_COMB (@lem13203 A) (@lem13202 A x y)). Qed.
Lemma lem13206 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem13207 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem13206 A t2 t1). Qed.
Lemma lem13208 {A : Type'} (x : A) (y : A) : (@COND A True y x) = y.
Proof. exact (@lem13207 A x y). Qed.
Lemma lem13209 {A : Type'} (x : A) (y : A) : ((term5 A x y) = (@COND A True y x)) = (y = y).
Proof. exact (MK_COMB (@lem13204 A x y) (@lem13208 A x y)). Qed.
Lemma lem13211 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem13212 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem13211 A x). Qed.
Lemma lem13213 {A : Type'} (y : A) : (y = y) = True.
Proof. exact (@lem13212 A y). Qed.
Lemma lem13214 {A : Type'} (y : A) (x : A) : ((term5 A x y) = (@COND A True y x)) = True.
Proof. exact (TRANS (@lem13209 A x y) (@lem13213 A y)). Qed.
Lemma lem13215 {A : Type'} (y : A) (x : A) : True = ((term5 A x y) = (@COND A True y x)).
Proof. exact (SYM (@lem13214 A y x)). Qed.
Lemma lem13216 {A : Type'} (y : A) (x : A) : (term5 A x y) = (@COND A True y x).
Proof. exact (EQ_MP (@lem13215 A y x) (@lem0)). Qed.
Lemma lem13220 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem13221 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem13222 {A : Type'} : (term14 A) = (@COND A True).
Proof. exact (MK_COMB (@lem13221 A) (@lem13220)). Qed.
Lemma lem13223 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem13224 {A : Type'} (x : A) : (term15 A x) = (@COND A True x).
Proof. exact (MK_COMB (@lem13222 A) (@lem13223 A x)). Qed.
Lemma lem13225 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem13226 {A : Type'} (x : A) (y : A) : (term10 A x y) = (@COND A True x y).
Proof. exact (MK_COMB (@lem13224 A x) (@lem13225 A y)). Qed.
Lemma lem13228 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem13229 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem13228 A t2 t1). Qed.
Lemma lem13230 {A : Type'} (y : A) (x : A) : (@COND A True x y) = x.
Proof. exact (@lem13229 A y x). Qed.
Lemma lem13231 {A : Type'} (y : A) (x : A) : (term10 A x y) = x.
Proof. exact (TRANS (@lem13226 A x y) (@lem13230 A y x)). Qed.
Lemma lem13232 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem13233 {A : Type'} (y : A) (x : A) : (term16 A x y) = (@eq A x).
Proof. exact (MK_COMB (@lem13232 A) (@lem13231 A y x)). Qed.
Lemma lem13235 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem13236 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem13235 A t1 t2). Qed.
Lemma lem13237 {A : Type'} (y : A) (x : A) : (@COND A False y x) = x.
Proof. exact (@lem13236 A y x). Qed.
Lemma lem13238 {A : Type'} (y : A) (x : A) : ((term10 A x y) = (@COND A False y x)) = (x = x).
Proof. exact (MK_COMB (@lem13233 A y x) (@lem13237 A y x)). Qed.
Lemma lem13240 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem13241 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem13240 A x). Qed.
Lemma lem13242 {A : Type'} (y : A) (x : A) : ((term10 A x y) = (@COND A False y x)) = True.
Proof. exact (TRANS (@lem13238 A y x) (@lem13241 A x)). Qed.
Lemma lem13243 {A : Type'} (y : A) (x : A) : True = ((term10 A x y) = (@COND A False y x)).
Proof. exact (SYM (@lem13242 A y x)). Qed.
Lemma lem13244 {A : Type'} (y : A) (x : A) : (term10 A x y) = (@COND A False y x).
Proof. exact (EQ_MP (@lem13243 A y x) (@lem0)). Qed.
Lemma lem13245 {A : Type'} (y : A) (x : A) (p : Prop) (h1 : p = False) : (term7 A p x y) = (@COND A p y x).
Proof. exact (EQ_MP (@lem13187 A y x p h1) (@lem13244 A y x)). Qed.
Lemma lem13246 {A : Type'} (y : A) (x : A) (p : Prop) (h1 : p = True) : (term7 A p x y) = (@COND A p y x).
Proof. exact (EQ_MP (@lem13174 A y x p h1) (@lem13216 A y x)). Qed.
Lemma lem13247 {A : Type'} (p : Prop) (y : A) (x : A) : (term7 A p x y) = (@COND A p y x).
Proof. exact (or_elim (@lem13159 p) (fun h0 : p = True => @lem13246 A y x p h0) (fun h0 : p = False => @lem13245 A y x p h0)). Qed.
Lemma lem13252 {A : Type'} (p : Prop) (x : A) : term17 A p x.
Proof. exact (fun y : A => @lem13247 A p y x). Qed.
Lemma lem13257 {A : Type'} (p : Prop) : term18 A p.
Proof. exact (fun x : A => @lem13252 A p x). Qed.
Lemma lem13262 {A : Type'} : term19 A.
Proof. exact (fun p : Prop => @lem13257 A p). Qed.
