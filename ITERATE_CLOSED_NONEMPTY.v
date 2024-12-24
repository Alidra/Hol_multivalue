Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_CLOSED_NONEMPTY_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import FORALL_IN_INSERT_spec.
Require Import ITERATE_CLAUSES_spec.
Require Import ITERATE_SING_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_INSERT_EMPTY_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm196_spec.
Require Import thm197_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem5807176 {A : Type'} (t : A -> Prop) : term0 A t.
Proof. exact (@lem9784 (t = (@EMPTY A))). Qed.
Lemma lem5807177 {A : Type'} (t : A -> Prop) : (term0 A t) = (term1 A t).
Proof. exact (eq_refl (term0 A t)). Qed.
Lemma lem5807178 {A : Type'} (t : A -> Prop) : term1 A t.
Proof. exact (EQ_MP (@lem5807177 A t) (@lem5807176 A t)). Qed.
Lemma lem5807180 {A : Type'} (t : A -> Prop) (h1 : term2 A t) : term2 A t.
Proof. exact (h1). Qed.
Lemma lem5807181 {A : Type'} (x : A) : term3 A x.
Proof. exact (@lem3278799 A x). Qed.
Lemma lem5807182 {A : Type'} (x : A) : (term3 A x) = (term4 A x).
Proof. exact (eq_refl (term3 A x)). Qed.
Lemma lem5807183 {A : Type'} (x : A) : term4 A x.
Proof. exact (EQ_MP (@lem5807182 A x) (@lem5807181 A x)). Qed.
Lemma lem5807184 {A : Type'} (x : A) (s : A -> Prop) : term5 A x s.
Proof. exact (@lem5807183 A x s). Qed.
Lemma lem5807185 {A : Type'} (x : A) (s : A -> Prop) : (term5 A x s) = (term6 A x s).
Proof. exact (eq_refl (term5 A x s)). Qed.
Lemma lem5807186 {A : Type'} (x : A) (s : A -> Prop) : term6 A x s.
Proof. exact (EQ_MP (@lem5807185 A x s) (@lem5807184 A x s)). Qed.
Lemma lem5807187 {A : Type'} (x : A) (s : A -> Prop) : term7 A x s.
Proof. exact (@lem82 ((@INSERT A x s) = (@EMPTY A))). Qed.
Lemma lem5807200 {A : Type'} (x : A) : term8 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem5807201 {A : Type'} (x : A) : (term8 A x) = (term9 A x).
Proof. exact (eq_refl (term8 A x)). Qed.
Lemma lem5807202 {A : Type'} (x : A) : term9 A x.
Proof. exact (EQ_MP (@lem5807201 A x) (@lem5807200 A x)). Qed.
Lemma lem5807203 {A : Type'} (x : A) : term10 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem5807205 {_83983 : Type'} (P : _83983 -> Prop) : term11 _83983 P.
Proof. exact (@lem3207453 _83983 P). Qed.
Lemma lem5807206 {_83983 : Type'} (P : _83983 -> Prop) : (term11 _83983 P) = (term12 _83983 P).
Proof. exact (eq_refl (term11 _83983 P)). Qed.
Lemma lem5807207 {_83983 : Type'} (P : _83983 -> Prop) : term12 _83983 P.
Proof. exact (EQ_MP (@lem5807206 _83983 P) (@lem5807205 _83983 P)). Qed.
Lemma lem5807208 {_83983 : Type'} (P : _83983 -> Prop) (a : _83983) : term13 _83983 P a.
Proof. exact (@lem5807207 _83983 P a). Qed.
Lemma lem5807209 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : (term13 _83983 P a) = (term14 _83983 a P).
Proof. exact (eq_refl (term13 _83983 P a)). Qed.
Lemma lem5807210 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : term14 _83983 a P.
Proof. exact (EQ_MP (@lem5807209 _83983 a P) (@lem5807208 _83983 P a)). Qed.
Lemma lem5807211 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) (s : _83983 -> Prop) : term15 _83983 a P s.
Proof. exact (@lem5807210 _83983 a P s). Qed.
Lemma lem5807212 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term15 _83983 a P s) = ((term16 _83983 a s P) = (term17 _83983 a s P)).
Proof. exact (eq_refl (term15 _83983 a P s)). Qed.
Lemma lem5807214 {A : Type'} (h1 : term18 A) : term18 A.
Proof. exact (h1). Qed.
Lemma lem5807215 {A : Type'} (P : type686 A) (h1 : term18 A) : term19 A P.
Proof. exact (@lem5807214 A h1 P). Qed.
Lemma lem5807216 {A : Type'} (P : type686 A) : (term19 A P) = (term20 A P).
Proof. exact (eq_refl (term19 A P)). Qed.
Lemma lem5807217 {A : Type'} (P : type686 A) (h1 : term18 A) : term20 A P.
Proof. exact (EQ_MP (@lem5807216 A P) (@lem5807215 A P h1)). Qed.
Lemma lem5807218 {A : Type'} (P : type686 A) (h1 : term21 A P) : term21 A P.
Proof. exact (h1). Qed.
Lemma lem5807219 {A : Type'} (P : type686 A) (h1 : term18 A) (h2 : term21 A P) : term22 A P.
Proof. exact (@lem5807217 A P h1 (@lem5807218 A P h2)). Qed.
Lemma lem5807220 {A : Type'} (P : type686 A) (h1 : term21 A P) : term23 A P.
Proof. exact (fun h0 : term18 A => @lem5807219 A P h0 h1). Qed.
Lemma lem5807221 {A : Type'} (h1 : term18 A) : term18 A.
Proof. exact (h1). Qed.
Lemma lem5807222 {A : Type'} (P : type686 A) (h1 : term18 A) (h2 : term21 A P) : term22 A P.
Proof. exact (@lem5807220 A P h2 (@lem5807221 A h1)). Qed.
Lemma lem5807223 {A : Type'} (P : type686 A) (h1 : term18 A) : term20 A P.
Proof. exact (fun h0 : term21 A P => @lem5807222 A P h1 h0). Qed.
Lemma lem5807224 {A : Type'} (h1 : term18 A) : term18 A.
Proof. exact (fun P : type686 A => @lem5807223 A P h1). Qed.
Lemma lem5807225 {A : Type'} : term24 A.
Proof. exact (fun h0 : term18 A => @lem5807224 A h0). Qed.
Lemma lem5807226 {A : Type'} : term18 A.
Proof. exact (@lem5807225 A (@lem3558722 A)). Qed.
Lemma lem5807227 {A : Type'} (P : type686 A) : term19 A P.
Proof. exact (@lem5807226 A P). Qed.
Lemma lem5807228 {A : Type'} (P : type686 A) : (term19 A P) = (term20 A P).
Proof. exact (eq_refl (term19 A P)). Qed.
Lemma lem5807230 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem5807231 {B : Type'} (P : B -> Prop) (op : type1400 B) (h1 : term25 B P op) : term25 B P op.
Proof. exact (h1). Qed.
Lemma lem5807237 (p : Prop) (q : Prop) (r : Prop) : (term26 p q r) = (term27 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem5807238 {A B : Type'} (P : B -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term28 A B P op s f) = (term29 A B P op s f).
Proof. exact (@lem5807237 (@FINITE A s) (term30 A B s P f) (term31 A B P op s f)). Qed.
Lemma lem5807242 (p : Prop) (q : Prop) (r : Prop) : (term26 p q r) = (term27 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem5807243 {A B : Type'} (P : B -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term32 A B P op s f) = (term33 A B P op s f).
Proof. exact (@lem5807242 (term2 A s) (term34 A B s P f) (term31 A B P op s f)). Qed.
Lemma lem5807256 {A : Type'} (s : A -> Prop) : (term35 A s) = (term35 A s).
Proof. exact (eq_refl (term35 A s)). Qed.
Lemma lem5807257 {A B : Type'} (P : B -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term29 A B P op s f) = (term36 A B P op s f).
Proof. exact (MK_COMB (@lem5807256 A s) (@lem5807243 A B P op s f)). Qed.
Lemma lem5807260 {A B : Type'} (P : B -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term28 A B P op s f) = (term36 A B P op s f).
Proof. exact (TRANS (@lem5807238 A B P op s f) (@lem5807257 A B P op s f)). Qed.
Lemma lem5807261 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term37 A B P op f) = (term38 A B P op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5807260 A B P op s f)). Qed.
Lemma lem5807262 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5807263 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term39 A B P op f) = (term40 A B P op f).
Proof. exact (MK_COMB (@lem5807262 A) (@lem5807261 A B P op f)). Qed.
Lemma lem5807268 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term40 A B P op f) = (term39 A B P op f).
Proof. exact (SYM (@lem5807263 A B P op f)). Qed.
Lemma lem5807270 {A : Type'} (P : type686 A) : term20 A P.
Proof. exact (EQ_MP (@lem5807228 A P) (@lem5807227 A P)). Qed.
Lemma lem5807271 {A : Type'} (P : type686 A) : term20 A P.
Proof. exact (@lem5807270 A P). Qed.
Lemma lem5807272 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : term41 A B P op f.
Proof. exact (@lem5807271 A (term42 A B P op f)). Qed.
Lemma lem5807273 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term43 A B P op f) = (term44 A B P op f).
Proof. exact (eq_refl (term43 A B P op f)). Qed.
Lemma lem5807274 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5807275 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term45 A B P op f) = (term46 A B P op f).
Proof. exact (MK_COMB (@lem5807274) (@lem5807273 A B P op f)). Qed.
Lemma lem5807276 {A B : Type'} (P : B -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term47 A B P op f s) = (term33 A B P op s f).
Proof. exact (eq_refl (term47 A B P op f s)). Qed.
Lemma lem5807277 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5807278 {A B : Type'} (P : B -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term48 A B P op f s) = (term49 A B P op s f).
Proof. exact (MK_COMB (@lem5807277) (@lem5807276 A B P op s f)). Qed.
Lemma lem5807279 {A : Type'} (x : A) (s : A -> Prop) : (term50 A x s) = (term50 A x s).
Proof. exact (eq_refl (term50 A x s)). Qed.
Lemma lem5807280 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) : (term51 A B P op f x s) = (term52 A B P op f x s).
Proof. exact (MK_COMB (@lem5807278 A B P op s f) (@lem5807279 A x s)). Qed.
Lemma lem5807281 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5807282 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) : (term53 A B P op f x s) = (term54 A B P op f x s).
Proof. exact (MK_COMB (@lem5807281) (@lem5807280 A B P op f x s)). Qed.
Lemma lem5807283 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : (term55 A B P op f x s) = (term56 A B P op x s f).
Proof. exact (eq_refl (term55 A B P op f x s)). Qed.
Lemma lem5807284 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : (term57 A B P op f x s) = (term58 A B P op x s f).
Proof. exact (MK_COMB (@lem5807282 A B P op f x s) (@lem5807283 A B P op x s f)). Qed.
Lemma lem5807285 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (f : A -> B) : (term59 A B P op f x) = (term60 A B P op x f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5807284 A B P op x s f)). Qed.
Lemma lem5807286 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5807287 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (f : A -> B) : (term61 A B P op f x) = (term62 A B P op x f).
Proof. exact (MK_COMB (@lem5807286 A) (@lem5807285 A B P op x f)). Qed.
Lemma lem5807288 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term63 A B P op f) = (term64 A B P op f).
Proof. exact (fun_ext (fun x : A => @lem5807287 A B P op x f)). Qed.
Lemma lem5807289 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5807290 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term65 A B P op f) = (term66 A B P op f).
Proof. exact (MK_COMB (@lem5807289 A) (@lem5807288 A B P op f)). Qed.
Lemma lem5807291 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term67 A B P op f) = (term68 A B P op f).
Proof. exact (MK_COMB (@lem5807275 A B P op f) (@lem5807290 A B P op f)). Qed.
Lemma lem5807292 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5807293 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term69 A B P op f) = (term70 A B P op f).
Proof. exact (MK_COMB (@lem5807292) (@lem5807291 A B P op f)). Qed.
Lemma lem5807294 {A B : Type'} (P : B -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term47 A B P op f s) = (term33 A B P op s f).
Proof. exact (eq_refl (term47 A B P op f s)). Qed.
Lemma lem5807295 {A : Type'} (s : A -> Prop) : (term35 A s) = (term35 A s).
Proof. exact (eq_refl (term35 A s)). Qed.
Lemma lem5807296 {A B : Type'} (P : B -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term71 A B P op f s) = (term36 A B P op s f).
Proof. exact (MK_COMB (@lem5807295 A s) (@lem5807294 A B P op s f)). Qed.
Lemma lem5807297 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term72 A B P op f) = (term38 A B P op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5807296 A B P op s f)). Qed.
Lemma lem5807298 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5807299 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term73 A B P op f) = (term40 A B P op f).
Proof. exact (MK_COMB (@lem5807298 A) (@lem5807297 A B P op f)). Qed.
Lemma lem5807300 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term41 A B P op f) = (term74 A B P op f).
Proof. exact (MK_COMB (@lem5807293 A B P op f) (@lem5807299 A B P op f)). Qed.
Lemma lem5807301 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : term74 A B P op f.
Proof. exact (EQ_MP (@lem5807300 A B P op f) (@lem5807272 A B P op f)). Qed.
Lemma lem5807307 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5807308 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem5807307 (A -> Prop) x). Qed.
Lemma lem5807309 {A : Type'} : ((@EMPTY A) = (@EMPTY A)) = True.
Proof. exact (@lem5807308 A (@EMPTY A)). Qed.
Lemma lem5807310 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5807311 {A : Type'} : (term75 A) = (~ True).
Proof. exact (MK_COMB (@lem5807310) (@lem5807309 A)). Qed.
Lemma lem5807313 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem5807314 {A : Type'} : (term75 A) = False.
Proof. exact (TRANS (@lem5807311 A) (@lem5807313)). Qed.
Lemma lem5807315 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5807316 {A : Type'} : (term76 A) = (imp False).
Proof. exact (MK_COMB (@lem5807315) (@lem5807314 A)). Qed.
Lemma lem5807326 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5807203 A x (@lem5807202 A x)). Qed.
Lemma lem5807327 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5807326 A x). Qed.
Lemma lem5807328 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5807329 {A : Type'} (x : A) : (term77 A x) = (imp False).
Proof. exact (MK_COMB (@lem5807328) (@lem5807327 A x)). Qed.
Lemma lem5807330 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term78 A B P f x) = (term78 A B P f x).
Proof. exact (eq_refl (term78 A B P f x)). Qed.
Lemma lem5807331 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term79 A B P f x) = (term80 A B P f x).
Proof. exact (MK_COMB (@lem5807329 A x) (@lem5807330 A B P f x)). Qed.
Lemma lem5807333 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem5807334 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term80 A B P f x) = True.
Proof. exact (@lem5807333 (term78 A B P f x)). Qed.
Lemma lem5807335 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term79 A B P f x) = True.
Proof. exact (TRANS (@lem5807331 A B P f x) (@lem5807334 A B P f x)). Qed.
Lemma lem5807336 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term81 A B P f) = (term82 A).
Proof. exact (fun_ext (fun x : A => @lem5807335 A B P f x)). Qed.
Lemma lem5807337 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5807338 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term83 A B P f) = (term84 A).
Proof. exact (MK_COMB (@lem5807337 A) (@lem5807336 A B P f)). Qed.
Lemma lem5807340 {A : Type'} (t : Prop) : (term85 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5807341 {A : Type'} (t : Prop) : (term85 A t) = t.
Proof. exact (@lem5807340 A t). Qed.
Lemma lem5807342 {A : Type'} : (term84 A) = True.
Proof. exact (@lem5807341 A True). Qed.
Lemma lem5807343 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term83 A B P f) = True.
Proof. exact (TRANS (@lem5807338 A B P f) (@lem5807342 A)). Qed.
Lemma lem5807344 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5807345 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term86 A B P f) = (imp True).
Proof. exact (MK_COMB (@lem5807344) (@lem5807343 A B P f)). Qed.
Lemma lem5807346 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term87 A B P op f) = (term87 A B P op f).
Proof. exact (eq_refl (term87 A B P op f)). Qed.
Lemma lem5807347 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term88 A B P op f) = (term89 A B P op f).
Proof. exact (MK_COMB (@lem5807345 A B P f) (@lem5807346 A B P op f)). Qed.
Lemma lem5807349 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem5807350 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term89 A B P op f) = (term87 A B P op f).
Proof. exact (@lem5807349 (term87 A B P op f)). Qed.
Lemma lem5807351 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term88 A B P op f) = (term87 A B P op f).
Proof. exact (TRANS (@lem5807347 A B P op f) (@lem5807350 A B P op f)). Qed.
Lemma lem5807352 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term44 A B P op f) = (term90 A B P op f).
Proof. exact (MK_COMB (@lem5807316 A) (@lem5807351 A B P op f)). Qed.
Lemma lem5807354 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem5807355 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term90 A B P op f) = True.
Proof. exact (@lem5807354 (term87 A B P op f)). Qed.
Lemma lem5807356 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term44 A B P op f) = True.
Proof. exact (TRANS (@lem5807352 A B P op f) (@lem5807355 A B P op f)). Qed.
Lemma lem5807357 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5807358 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term46 A B P op f) = (and True).
Proof. exact (MK_COMB (@lem5807357) (@lem5807356 A B P op f)). Qed.
Lemma lem5807388 {A : Type'} (x : A) (s : A -> Prop) : ((@INSERT A x s) = (@EMPTY A)) = False.
Proof. exact (@lem5807187 A x s (@lem5807186 A x s)). Qed.
Lemma lem5807389 {A : Type'} (x : A) (s : A -> Prop) : ((@INSERT A x s) = (@EMPTY A)) = False.
Proof. exact (@lem5807388 A x s). Qed.
Lemma lem5807390 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5807391 {A : Type'} (x : A) (s : A -> Prop) : (term6 A x s) = (~ False).
Proof. exact (MK_COMB (@lem5807390) (@lem5807389 A x s)). Qed.
Lemma lem5807393 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5807394 {A : Type'} (x : A) (s : A -> Prop) : (term6 A x s) = True.
Proof. exact (TRANS (@lem5807391 A x s) (@lem5807393)). Qed.
Lemma lem5807395 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5807396 {A : Type'} (x : A) (s : A -> Prop) : (term91 A x s) = (imp True).
Proof. exact (MK_COMB (@lem5807395) (@lem5807394 A x s)). Qed.
Lemma lem5807400 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term16 _83983 a s P) = (term17 _83983 a s P).
Proof. exact (EQ_MP (@lem5807212 _83983 a s P) (@lem5807211 _83983 a P s)). Qed.
Lemma lem5807401 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term16 A a s P) = (term17 A a s P).
Proof. exact (@lem5807400 A a s P). Qed.
Lemma lem5807402 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term92 A B x s P f) = (term93 A B x s P f).
Proof. exact (@lem5807401 A x s (term94 A B P f)). Qed.
Lemma lem5807403 {A B : Type'} (P : B -> Prop) (f : A -> B) (x' : A) : (term95 A B P f x') = (term78 A B P f x').
Proof. exact (eq_refl (term95 A B P f x')). Qed.
Lemma lem5807404 {A : Type'} (x' : A) (x : A) (s : A -> Prop) : (term96 A x' x s) = (term96 A x' x s).
Proof. exact (eq_refl (term96 A x' x s)). Qed.
Lemma lem5807405 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) : (term97 A B x s P f x') = (term98 A B x s P f x').
Proof. exact (MK_COMB (@lem5807404 A x' x s) (@lem5807403 A B P f x')). Qed.
Lemma lem5807406 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term99 A B x s P f) = (term100 A B x s P f).
Proof. exact (fun_ext (fun x' : A => @lem5807405 A B x s P f x')). Qed.
Lemma lem5807407 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5807408 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term92 A B x s P f) = (term101 A B x s P f).
Proof. exact (MK_COMB (@lem5807407 A) (@lem5807406 A B x s P f)). Qed.
Lemma lem5807409 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5807410 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term102 A B x s P f) = (term103 A B x s P f).
Proof. exact (MK_COMB (@lem5807409) (@lem5807408 A B x s P f)). Qed.
Lemma lem5807411 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term95 A B P f x) = (term78 A B P f x).
Proof. exact (eq_refl (term95 A B P f x)). Qed.
Lemma lem5807412 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5807413 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term104 A B P f x) = (term105 A B P f x).
Proof. exact (MK_COMB (@lem5807412) (@lem5807411 A B P f x)). Qed.
Lemma lem5807414 {A B : Type'} (P : B -> Prop) (f : A -> B) (x' : A) : (term95 A B P f x') = (term78 A B P f x').
Proof. exact (eq_refl (term95 A B P f x')). Qed.
Lemma lem5807415 {A : Type'} (x' : A) (s : A -> Prop) : (term106 A x' s) = (term106 A x' s).
Proof. exact (eq_refl (term106 A x' s)). Qed.
Lemma lem5807416 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) : (term107 A B s P f x') = (term108 A B s P f x').
Proof. exact (MK_COMB (@lem5807415 A x' s) (@lem5807414 A B P f x')). Qed.
Lemma lem5807417 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term109 A B s P f) = (term110 A B s P f).
Proof. exact (fun_ext (fun x' : A => @lem5807416 A B s P f x')). Qed.
Lemma lem5807418 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5807419 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term111 A B s P f) = (term34 A B s P f).
Proof. exact (MK_COMB (@lem5807418 A) (@lem5807417 A B s P f)). Qed.
Lemma lem5807420 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term93 A B x s P f) = (term112 A B x s P f).
Proof. exact (MK_COMB (@lem5807413 A B P f x) (@lem5807419 A B s P f)). Qed.
Lemma lem5807421 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((term92 A B x s P f) = (term93 A B x s P f)) = ((term101 A B x s P f) = (term112 A B x s P f)).
Proof. exact (MK_COMB (@lem5807410 A B x s P f) (@lem5807420 A B x s P f)). Qed.
Lemma lem5807422 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term101 A B x s P f) = (term112 A B x s P f).
Proof. exact (EQ_MP (@lem5807421 A B x s P f) (@lem5807402 A B x s P f)). Qed.
Lemma lem5807431 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5807432 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term113 A B x s P f) = (term114 A B x s P f).
Proof. exact (MK_COMB (@lem5807431) (@lem5807422 A B x s P f)). Qed.
Lemma lem5807433 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : (term115 A B P op x s f) = (term115 A B P op x s f).
Proof. exact (eq_refl (term115 A B P op x s f)). Qed.
Lemma lem5807434 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : (term116 A B P op x s f) = (term117 A B P op x s f).
Proof. exact (MK_COMB (@lem5807432 A B x s P f) (@lem5807433 A B P op x s f)). Qed.
Lemma lem5807437 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : (term56 A B P op x s f) = (term118 A B P op x s f).
Proof. exact (MK_COMB (@lem5807396 A x s) (@lem5807434 A B P op x s f)). Qed.
Lemma lem5807439 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem5807440 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : (term118 A B P op x s f) = (term117 A B P op x s f).
Proof. exact (@lem5807439 (term117 A B P op x s f)). Qed.
Lemma lem5807451 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : (term56 A B P op x s f) = (term117 A B P op x s f).
Proof. exact (TRANS (@lem5807437 A B P op x s f) (@lem5807440 A B P op x s f)). Qed.
Lemma lem5807452 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) : (term54 A B P op f x s) = (term54 A B P op f x s).
Proof. exact (eq_refl (term54 A B P op f x s)). Qed.
Lemma lem5807453 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : (term58 A B P op x s f) = (term119 A B P op x s f).
Proof. exact (MK_COMB (@lem5807452 A B P op f x s) (@lem5807451 A B P op x s f)). Qed.
Lemma lem5807456 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (f : A -> B) : (term60 A B P op x f) = (term120 A B P op x f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5807453 A B P op x s f)). Qed.
Lemma lem5807457 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5807458 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (f : A -> B) : (term62 A B P op x f) = (term121 A B P op x f).
Proof. exact (MK_COMB (@lem5807457 A) (@lem5807456 A B P op x f)). Qed.
Lemma lem5807463 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term64 A B P op f) = (term122 A B P op f).
Proof. exact (fun_ext (fun x : A => @lem5807458 A B P op x f)). Qed.
Lemma lem5807464 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5807465 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term66 A B P op f) = (term123 A B P op f).
Proof. exact (MK_COMB (@lem5807464 A) (@lem5807463 A B P op f)). Qed.
Lemma lem5807470 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term68 A B P op f) = (term124 A B P op f).
Proof. exact (MK_COMB (@lem5807358 A B P op f) (@lem5807465 A B P op f)). Qed.
Lemma lem5807472 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5807473 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term124 A B P op f) = (term123 A B P op f).
Proof. exact (@lem5807472 (term123 A B P op f)). Qed.
Lemma lem5807510 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term68 A B P op f) = (term123 A B P op f).
Proof. exact (TRANS (@lem5807470 A B P op f) (@lem5807473 A B P op f)). Qed.
Lemma lem5807511 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term123 A B P op f) = (term68 A B P op f).
Proof. exact (SYM (@lem5807510 A B P op f)). Qed.
Lemma lem5807512 {A B : Type'} (op : type1400 B) : term125 A B op.
Proof. exact (@lem5807175 A B op). Qed.
Lemma lem5807513 {A B : Type'} (op : type1400 B) : (term125 A B op) = (term126 A B op).
Proof. exact (eq_refl (term125 A B op)). Qed.
Lemma lem5807514 {A B : Type'} (op : type1400 B) : term126 A B op.
Proof. exact (EQ_MP (@lem5807513 A B op) (@lem5807512 A B op)). Qed.
Lemma lem5807515 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem5807516 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term127 A B op.
Proof. exact (@lem5807514 A B op (@lem5807515 B op h1)). Qed.
Lemma lem5807517 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term128 A B op f.
Proof. exact (@lem5807516 A B op h1 f). Qed.
Lemma lem5807518 {A B : Type'} (op : type1400 B) (f : A -> B) : (term128 A B op f) = (term129 A B op f).
Proof. exact (eq_refl (term128 A B op f)). Qed.
Lemma lem5807519 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term129 A B op f.
Proof. exact (EQ_MP (@lem5807518 A B op f) (@lem5807517 A B f op h1)). Qed.
Lemma lem5807520 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (h1 : @monoidal B op) : term130 A B op f x.
Proof. exact (@lem5807519 A B f op h1 x). Qed.
Lemma lem5807521 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) : (term130 A B op f x) = ((term131 A B op x f) = (f x)).
Proof. exact (eq_refl (term130 A B op f x)). Qed.
Lemma lem5807522 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (h1 : @monoidal B op) : (term131 A B op x f) = (f x).
Proof. exact (EQ_MP (@lem5807521 A B op f x) (@lem5807520 A B f x op h1)). Qed.
Lemma lem5807528 {B : Type'} (op : type1400 B) : (@monoidal B op) = ((@monoidal B op) = True).
Proof. exact (@lem7 (@monoidal B op)). Qed.
Lemma lem5807548 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term132 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5807549 (p : Prop) (q : Prop) (p' : Prop) : term133 p q p'.
Proof. exact (fun q' : Prop => @lem5807548 p q p' q'). Qed.
Lemma lem5807550 (p : Prop) (q : Prop) : term134 p q.
Proof. exact (fun p' : Prop => @lem5807549 p q p'). Qed.
Lemma lem5807551 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) : term135 A B P op a t f.
Proof. exact (@lem5807550 (term52 A B P op f a t) (term117 A B P op a t f)). Qed.
Lemma lem5807552 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) (p' : Prop) : term136 A B P op a t f p'.
Proof. exact (@lem5807551 A B P op a t f p'). Qed.
Lemma lem5807553 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) (p' : Prop) : (term136 A B P op a t f p') = (term137 A B P op a t f p').
Proof. exact (eq_refl (term136 A B P op a t f p')). Qed.
Lemma lem5807554 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) (p' : Prop) : term137 A B P op a t f p'.
Proof. exact (EQ_MP (@lem5807553 A B P op a t f p') (@lem5807552 A B P op a t f p')). Qed.
Lemma lem5807555 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term138 A B P op a t f p' q'.
Proof. exact (@lem5807554 A B P op a t f p' q'). Qed.
Lemma lem5807556 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : (term138 A B P op a t f p' q') = (term139 A B P op a t f p' q').
Proof. exact (eq_refl (term138 A B P op a t f p' q')). Qed.
Lemma lem5807557 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term139 A B P op a t f p' q'.
Proof. exact (EQ_MP (@lem5807556 A B P op a t f p' q') (@lem5807555 A B P op a t f p' q')). Qed.
Lemma lem5807563 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term132 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5807564 (p : Prop) (q : Prop) (p' : Prop) : term133 p q p'.
Proof. exact (fun q' : Prop => @lem5807563 p q p' q'). Qed.
Lemma lem5807565 (p : Prop) (q : Prop) : term134 p q.
Proof. exact (fun p' : Prop => @lem5807564 p q p'). Qed.
Lemma lem5807566 {A B : Type'} (P : B -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) : term140 A B P op t f.
Proof. exact (@lem5807565 (term2 A t) (term141 A B P op t f)). Qed.
Lemma lem5807567 {A B : Type'} (P : B -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) (p' : Prop) : term142 A B P op t f p'.
Proof. exact (@lem5807566 A B P op t f p'). Qed.
Lemma lem5807568 {A B : Type'} (P : B -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) (p' : Prop) : (term142 A B P op t f p') = (term143 A B P op t f p').
Proof. exact (eq_refl (term142 A B P op t f p')). Qed.
Lemma lem5807569 {A B : Type'} (P : B -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) (p' : Prop) : term143 A B P op t f p'.
Proof. exact (EQ_MP (@lem5807568 A B P op t f p') (@lem5807567 A B P op t f p')). Qed.
Lemma lem5807570 {A B : Type'} (P : B -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term144 A B P op t f p' q'.
Proof. exact (@lem5807569 A B P op t f p' q'). Qed.
Lemma lem5807571 {A B : Type'} (P : B -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : (term144 A B P op t f p' q') = (term145 A B P op t f p' q').
Proof. exact (eq_refl (term144 A B P op t f p' q')). Qed.
Lemma lem5807572 {A B : Type'} (P : B -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term145 A B P op t f p' q'.
Proof. exact (EQ_MP (@lem5807571 A B P op t f p' q') (@lem5807570 A B P op t f p' q')). Qed.
Lemma lem5807576 {A : Type'} (t : A -> Prop) (h1 : t = (@EMPTY A)) : t = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem5807577 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem5807578 {A : Type'} (t : A -> Prop) (h1 : t = (@EMPTY A)) : (@eq (A -> Prop) t) = (@eq (A -> Prop) (@EMPTY A)).
Proof. exact (MK_COMB (@lem5807577 A) (@lem5807576 A t h1)). Qed.
Lemma lem5807579 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (eq_refl (@EMPTY A)). Qed.
Lemma lem5807580 {A : Type'} (t : A -> Prop) (h1 : t = (@EMPTY A)) : (t = (@EMPTY A)) = ((@EMPTY A) = (@EMPTY A)).
Proof. exact (MK_COMB (@lem5807578 A t h1) (@lem5807579 A)). Qed.
Lemma lem5807582 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5807583 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem5807582 (A -> Prop) x). Qed.
Lemma lem5807584 {A : Type'} : ((@EMPTY A) = (@EMPTY A)) = True.
Proof. exact (@lem5807583 A (@EMPTY A)). Qed.
Lemma lem5807585 {A : Type'} (t : A -> Prop) (h1 : t = (@EMPTY A)) : (t = (@EMPTY A)) = True.
Proof. exact (TRANS (@lem5807580 A t h1) (@lem5807584 A)). Qed.
Lemma lem5807586 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5807587 {A : Type'} (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term2 A t) = (~ True).
Proof. exact (MK_COMB (@lem5807586) (@lem5807585 A t h1)). Qed.
Lemma lem5807589 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem5807590 {A : Type'} (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term2 A t) = False.
Proof. exact (TRANS (@lem5807587 A t h1) (@lem5807589)). Qed.
Lemma lem5807591 {A B : Type'} (P : B -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) (q' : Prop) : term146 A B P op t f q'.
Proof. exact (@lem5807572 A B P op t f False q'). Qed.
Lemma lem5807592 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (q' : Prop) (t : A -> Prop) (h1 : t = (@EMPTY A)) : term147 A B P op t f q'.
Proof. exact (@lem5807591 A B P op t f q' (@lem5807590 A t h1)). Qed.
Lemma lem5807599 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term132 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5807600 (p : Prop) (q : Prop) (p' : Prop) : term133 p q p'.
Proof. exact (fun q' : Prop => @lem5807599 p q p' q'). Qed.
Lemma lem5807601 (p : Prop) (q : Prop) : term134 p q.
Proof. exact (fun p' : Prop => @lem5807600 p q p'). Qed.
Lemma lem5807602 {A B : Type'} (P : B -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) : term148 A B P op t f.
Proof. exact (@lem5807601 (term34 A B t P f) (term31 A B P op t f)). Qed.
Lemma lem5807603 {A B : Type'} (P : B -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) (p' : Prop) : term149 A B P op t f p'.
Proof. exact (@lem5807602 A B P op t f p'). Qed.
Lemma lem5807604 {A B : Type'} (P : B -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) (p' : Prop) : (term149 A B P op t f p') = (term150 A B P op t f p').
Proof. exact (eq_refl (term149 A B P op t f p')). Qed.
Lemma lem5807605 {A B : Type'} (P : B -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) (p' : Prop) : term150 A B P op t f p'.
Proof. exact (EQ_MP (@lem5807604 A B P op t f p') (@lem5807603 A B P op t f p')). Qed.
Lemma lem5807606 {A B : Type'} (P : B -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term151 A B P op t f p' q'.
Proof. exact (@lem5807605 A B P op t f p' q'). Qed.
Lemma lem5807607 {A B : Type'} (P : B -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : (term151 A B P op t f p' q') = (term152 A B P op t f p' q').
Proof. exact (eq_refl (term151 A B P op t f p' q')). Qed.
Lemma lem5807608 {A B : Type'} (P : B -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term152 A B P op t f p' q'.
Proof. exact (EQ_MP (@lem5807607 A B P op t f p' q') (@lem5807606 A B P op t f p' q')). Qed.
Lemma lem5807616 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term132 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5807617 (p : Prop) (q : Prop) (p' : Prop) : term133 p q p'.
Proof. exact (fun q' : Prop => @lem5807616 p q p' q'). Qed.
Lemma lem5807618 (p : Prop) (q : Prop) : term134 p q.
Proof. exact (fun p' : Prop => @lem5807617 p q p'). Qed.
Lemma lem5807619 {A B : Type'} (t : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : term153 A B t P f x.
Proof. exact (@lem5807618 (@IN A x t) (term78 A B P f x)). Qed.
Lemma lem5807620 {A B : Type'} (t : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) (p' : Prop) : term154 A B t P f x p'.
Proof. exact (@lem5807619 A B t P f x p'). Qed.
Lemma lem5807621 {A B : Type'} (t : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) (p' : Prop) : (term154 A B t P f x p') = (term155 A B t P f x p').
Proof. exact (eq_refl (term154 A B t P f x p')). Qed.
Lemma lem5807622 {A B : Type'} (t : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) (p' : Prop) : term155 A B t P f x p'.
Proof. exact (EQ_MP (@lem5807621 A B t P f x p') (@lem5807620 A B t P f x p')). Qed.
Lemma lem5807623 {A B : Type'} (t : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) (p' : Prop) (q' : Prop) : term156 A B t P f x p' q'.
Proof. exact (@lem5807622 A B t P f x p' q'). Qed.
Lemma lem5807624 {A B : Type'} (t : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) (p' : Prop) (q' : Prop) : (term156 A B t P f x p' q') = (term157 A B t P f x p' q').
Proof. exact (eq_refl (term156 A B t P f x p' q')). Qed.
Lemma lem5807625 {A B : Type'} (t : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) (p' : Prop) (q' : Prop) : term157 A B t P f x p' q'.
Proof. exact (EQ_MP (@lem5807624 A B t P f x p' q') (@lem5807623 A B t P f x p' q')). Qed.
Lemma lem5807627 {A : Type'} (t : A -> Prop) (h1 : t = (@EMPTY A)) : t = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem5807628 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem5807629 {A : Type'} (x : A) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (@IN A x t) = (@IN A x (@EMPTY A)).
Proof. exact (MK_COMB (@lem5807628 A x) (@lem5807627 A t h1)). Qed.
Lemma lem5807630 {A B : Type'} (t : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) (q' : Prop) : term158 A B t P f x q'.
Proof. exact (@lem5807625 A B t P f x (@IN A x (@EMPTY A)) q'). Qed.
Lemma lem5807631 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) (q' : Prop) (t : A -> Prop) (h1 : t = (@EMPTY A)) : term159 A B t P f x q'.
Proof. exact (@lem5807630 A B t P f x q' (@lem5807629 A x t h1)). Qed.
Lemma lem5807635 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term78 A B P f x) = (term78 A B P f x).
Proof. exact (eq_refl (term78 A B P f x)). Qed.
Lemma lem5807636 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : term160 A B P f x.
Proof. exact (fun h0 : @IN A x (@EMPTY A) => @lem5807635 A B P f x). Qed.
Lemma lem5807637 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) (t : A -> Prop) (h1 : t = (@EMPTY A)) : term161 A B t P f x.
Proof. exact (@lem5807631 A B P f x (term78 A B P f x) t h1). Qed.
Lemma lem5807638 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term108 A B t P f x) = (term79 A B P f x).
Proof. exact (@lem5807637 A B P f x t h1 (@lem5807636 A B P f x)). Qed.
Lemma lem5807662 {A B : Type'} (P : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term110 A B t P f) = (term81 A B P f).
Proof. exact (fun_ext (fun x : A => @lem5807638 A B P f x t h1)). Qed.
Lemma lem5807686 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5807687 {A B : Type'} (P : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term34 A B t P f) = (term83 A B P f).
Proof. exact (MK_COMB (@lem5807686 A) (@lem5807662 A B P f t h1)). Qed.
Lemma lem5807715 {A B : Type'} (op : type1400 B) (t : A -> Prop) (P : B -> Prop) (f : A -> B) (q' : Prop) : term162 A B op t P f q'.
Proof. exact (@lem5807608 A B P op t f (term83 A B P f) q'). Qed.
Lemma lem5807716 {A B : Type'} (op : type1400 B) (P : B -> Prop) (f : A -> B) (q' : Prop) (t : A -> Prop) (h1 : t = (@EMPTY A)) : term163 A B op t P f q'.
Proof. exact (@lem5807715 A B op t P f q' (@lem5807687 A B P f t h1)). Qed.
Lemma lem5807731 {A : Type'} (t : A -> Prop) (h1 : t = (@EMPTY A)) : t = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem5807732 {A B : Type'} (op : type1400 B) : (@iterate B A op) = (@iterate B A op).
Proof. exact (eq_refl (@iterate B A op)). Qed.
Lemma lem5807733 {A B : Type'} (op : type1400 B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (@iterate B A op t) = (@iterate B A op (@EMPTY A)).
Proof. exact (MK_COMB (@lem5807732 A B op) (@lem5807731 A t h1)). Qed.
Lemma lem5807734 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5807735 {A B : Type'} (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (@iterate B A op t f) = (@iterate B A op (@EMPTY A) f).
Proof. exact (MK_COMB (@lem5807733 A B op t h1) (@lem5807734 A B f)). Qed.
Lemma lem5807736 {B : Type'} (P : B -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem5807737 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term31 A B P op t f) = (term87 A B P op f).
Proof. exact (MK_COMB (@lem5807736 B P) (@lem5807735 A B op f t h1)). Qed.
Lemma lem5807738 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : term164 A B t P op f.
Proof. exact (fun h0 : term83 A B P f => @lem5807737 A B P op f t h1). Qed.
Lemma lem5807739 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : term165 A B t P op f.
Proof. exact (@lem5807716 A B op P f (term87 A B P op f) t h1). Qed.
Lemma lem5807740 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term141 A B P op t f) = (term88 A B P op f).
Proof. exact (@lem5807739 A B P op f t h1 (@lem5807738 A B P op f t h1)). Qed.
Lemma lem5807828 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : term166 A B t P op f.
Proof. exact (fun h0 : False => @lem5807740 A B P op f t h1). Qed.
Lemma lem5807829 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : term167 A B t P op f.
Proof. exact (@lem5807592 A B P op f (term88 A B P op f) t h1). Qed.
Lemma lem5807830 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term33 A B P op t f) = (term168 A B P op f).
Proof. exact (@lem5807829 A B P op f t h1 (@lem5807828 A B P op f t h1)). Qed.
Lemma lem5807832 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem5807833 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term168 A B P op f) = True.
Proof. exact (@lem5807832 (term88 A B P op f)). Qed.
Lemma lem5807834 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term33 A B P op t f) = True.
Proof. exact (TRANS (@lem5807830 A B P op f t h1) (@lem5807833 A B P op f)). Qed.
Lemma lem5807835 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5807836 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term49 A B P op t f) = (and True).
Proof. exact (MK_COMB (@lem5807835) (@lem5807834 A B P op f t h1)). Qed.
Lemma lem5807840 {A : Type'} (t : A -> Prop) (h1 : t = (@EMPTY A)) : t = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem5807841 {A : Type'} (a : A) : (@IN A a) = (@IN A a).
Proof. exact (eq_refl (@IN A a)). Qed.
Lemma lem5807842 {A : Type'} (a : A) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (@IN A a t) = (@IN A a (@EMPTY A)).
Proof. exact (MK_COMB (@lem5807841 A a) (@lem5807840 A t h1)). Qed.
Lemma lem5807843 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5807844 {A : Type'} (a : A) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term169 A a t) = (term9 A a).
Proof. exact (MK_COMB (@lem5807843) (@lem5807842 A a t h1)). Qed.
Lemma lem5807845 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5807846 {A : Type'} (a : A) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term170 A a t) = (term171 A a).
Proof. exact (MK_COMB (@lem5807845) (@lem5807844 A a t h1)). Qed.
Lemma lem5807848 {A : Type'} (t : A -> Prop) (h1 : t = (@EMPTY A)) : t = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem5807849 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem5807850 {A : Type'} (t : A -> Prop) (h1 : t = (@EMPTY A)) : (@FINITE A t) = (@FINITE A (@EMPTY A)).
Proof. exact (MK_COMB (@lem5807849 A) (@lem5807848 A t h1)). Qed.
Lemma lem5807851 {A : Type'} (a : A) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term50 A a t) = (term172 A a).
Proof. exact (MK_COMB (@lem5807846 A a t h1) (@lem5807850 A t h1)). Qed.
Lemma lem5807854 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term52 A B P op f a t) = (term173 A a).
Proof. exact (MK_COMB (@lem5807836 A B P op f t h1) (@lem5807851 A a t h1)). Qed.
Lemma lem5807856 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5807857 {A : Type'} (a : A) : (term173 A a) = (term172 A a).
Proof. exact (@lem5807856 (term172 A a)). Qed.
Lemma lem5807860 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term52 A B P op f a t) = (term172 A a).
Proof. exact (TRANS (@lem5807854 A B P op f a t h1) (@lem5807857 A a)). Qed.
Lemma lem5807861 {A B : Type'} (P : B -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) (a : A) (q' : Prop) : term174 A B P op t f a q'.
Proof. exact (@lem5807557 A B P op a t f (term172 A a) q'). Qed.
Lemma lem5807862 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (q' : Prop) (t : A -> Prop) (h1 : t = (@EMPTY A)) : term175 A B P op t f a q'.
Proof. exact (@lem5807861 A B P op t f a q' (@lem5807860 A B P op f a t h1)). Qed.
Lemma lem5807873 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term132 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5807874 (p : Prop) (q : Prop) (p' : Prop) : term133 p q p'.
Proof. exact (fun q' : Prop => @lem5807873 p q p' q'). Qed.
Lemma lem5807875 (p : Prop) (q : Prop) : term134 p q.
Proof. exact (fun p' : Prop => @lem5807874 p q p'). Qed.
Lemma lem5807876 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) : term176 A B P op a t f.
Proof. exact (@lem5807875 (term112 A B a t P f) (term115 A B P op a t f)). Qed.
Lemma lem5807877 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) (p' : Prop) : term177 A B P op a t f p'.
Proof. exact (@lem5807876 A B P op a t f p'). Qed.
Lemma lem5807878 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) (p' : Prop) : (term177 A B P op a t f p') = (term178 A B P op a t f p').
Proof. exact (eq_refl (term177 A B P op a t f p')). Qed.
Lemma lem5807879 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) (p' : Prop) : term178 A B P op a t f p'.
Proof. exact (EQ_MP (@lem5807878 A B P op a t f p') (@lem5807877 A B P op a t f p')). Qed.
Lemma lem5807880 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term179 A B P op a t f p' q'.
Proof. exact (@lem5807879 A B P op a t f p' q'). Qed.
Lemma lem5807881 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : (term179 A B P op a t f p' q') = (term180 A B P op a t f p' q').
Proof. exact (eq_refl (term179 A B P op a t f p' q')). Qed.
Lemma lem5807882 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term180 A B P op a t f p' q'.
Proof. exact (EQ_MP (@lem5807881 A B P op a t f p' q') (@lem5807880 A B P op a t f p' q')). Qed.
Lemma lem5807892 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term132 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5807893 (p : Prop) (q : Prop) (p' : Prop) : term133 p q p'.
Proof. exact (fun q' : Prop => @lem5807892 p q p' q'). Qed.
Lemma lem5807894 (p : Prop) (q : Prop) : term134 p q.
Proof. exact (fun p' : Prop => @lem5807893 p q p'). Qed.
Lemma lem5807895 {A B : Type'} (t : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) : term153 A B t P f x'.
Proof. exact (@lem5807894 (@IN A x' t) (term78 A B P f x')). Qed.
Lemma lem5807896 {A B : Type'} (t : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (p' : Prop) : term154 A B t P f x' p'.
Proof. exact (@lem5807895 A B t P f x' p'). Qed.
Lemma lem5807897 {A B : Type'} (t : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (p' : Prop) : (term154 A B t P f x' p') = (term155 A B t P f x' p').
Proof. exact (eq_refl (term154 A B t P f x' p')). Qed.
Lemma lem5807898 {A B : Type'} (t : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (p' : Prop) : term155 A B t P f x' p'.
Proof. exact (EQ_MP (@lem5807897 A B t P f x' p') (@lem5807896 A B t P f x' p')). Qed.
Lemma lem5807899 {A B : Type'} (t : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (p' : Prop) (q' : Prop) : term156 A B t P f x' p' q'.
Proof. exact (@lem5807898 A B t P f x' p' q'). Qed.
Lemma lem5807900 {A B : Type'} (t : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (p' : Prop) (q' : Prop) : (term156 A B t P f x' p' q') = (term157 A B t P f x' p' q').
Proof. exact (eq_refl (term156 A B t P f x' p' q')). Qed.
Lemma lem5807901 {A B : Type'} (t : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (p' : Prop) (q' : Prop) : term157 A B t P f x' p' q'.
Proof. exact (EQ_MP (@lem5807900 A B t P f x' p' q') (@lem5807899 A B t P f x' p' q')). Qed.
Lemma lem5807903 {A : Type'} (t : A -> Prop) (h1 : t = (@EMPTY A)) : t = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem5807904 {A : Type'} (x' : A) : (@IN A x') = (@IN A x').
Proof. exact (eq_refl (@IN A x')). Qed.
Lemma lem5807905 {A : Type'} (x' : A) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (@IN A x' t) = (@IN A x' (@EMPTY A)).
Proof. exact (MK_COMB (@lem5807904 A x') (@lem5807903 A t h1)). Qed.
Lemma lem5807906 {A B : Type'} (t : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (q' : Prop) : term158 A B t P f x' q'.
Proof. exact (@lem5807901 A B t P f x' (@IN A x' (@EMPTY A)) q'). Qed.
Lemma lem5807907 {A B : Type'} (P : B -> Prop) (f : A -> B) (x' : A) (q' : Prop) (t : A -> Prop) (h1 : t = (@EMPTY A)) : term159 A B t P f x' q'.
Proof. exact (@lem5807906 A B t P f x' q' (@lem5807905 A x' t h1)). Qed.
Lemma lem5807911 {A B : Type'} (P : B -> Prop) (f : A -> B) (x' : A) : (term78 A B P f x') = (term78 A B P f x').
Proof. exact (eq_refl (term78 A B P f x')). Qed.
Lemma lem5807912 {A B : Type'} (P : B -> Prop) (f : A -> B) (x' : A) : term160 A B P f x'.
Proof. exact (fun h0 : @IN A x' (@EMPTY A) => @lem5807911 A B P f x'). Qed.
Lemma lem5807913 {A B : Type'} (P : B -> Prop) (f : A -> B) (x' : A) (t : A -> Prop) (h1 : t = (@EMPTY A)) : term161 A B t P f x'.
Proof. exact (@lem5807907 A B P f x' (term78 A B P f x') t h1). Qed.
Lemma lem5807914 {A B : Type'} (P : B -> Prop) (f : A -> B) (x' : A) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term108 A B t P f x') = (term79 A B P f x').
Proof. exact (@lem5807913 A B P f x' t h1 (@lem5807912 A B P f x')). Qed.
Lemma lem5807938 {A B : Type'} (P : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term110 A B t P f) = (term81 A B P f).
Proof. exact (fun_ext (fun x' : A => @lem5807914 A B P f x' t h1)). Qed.
Lemma lem5807962 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5807963 {A B : Type'} (P : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term34 A B t P f) = (term83 A B P f).
Proof. exact (MK_COMB (@lem5807962 A) (@lem5807938 A B P f t h1)). Qed.
Lemma lem5807991 {A B : Type'} (P : B -> Prop) (f : A -> B) (a : A) : (term105 A B P f a) = (term105 A B P f a).
Proof. exact (eq_refl (term105 A B P f a)). Qed.
Lemma lem5807992 {A B : Type'} (a : A) (P : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term112 A B a t P f) = (term181 A B a P f).
Proof. exact (MK_COMB (@lem5807991 A B P f a) (@lem5807963 A B P f t h1)). Qed.
Lemma lem5808022 {A B : Type'} (op : type1400 B) (t : A -> Prop) (a : A) (P : B -> Prop) (f : A -> B) (q' : Prop) : term182 A B op t a P f q'.
Proof. exact (@lem5807882 A B P op a t f (term181 A B a P f) q'). Qed.
Lemma lem5808023 {A B : Type'} (op : type1400 B) (a : A) (P : B -> Prop) (f : A -> B) (q' : Prop) (t : A -> Prop) (h1 : t = (@EMPTY A)) : term183 A B op t a P f q'.
Proof. exact (@lem5808022 A B op t a P f q' (@lem5807992 A B a P f t h1)). Qed.
Lemma lem5808024 {A B : Type'} (a : A) (P : B -> Prop) (f : A -> B) (h1 : term181 A B a P f) : term181 A B a P f.
Proof. exact (h1). Qed.
Lemma lem5808038 {A B : Type'} (a : A) (P : B -> Prop) (f : A -> B) (h1 : term181 A B a P f) : term78 A B P f a.
Proof. exact (proj1 (@lem5808024 A B a P f h1)). Qed.
Lemma lem5808039 {A B : Type'} (P : B -> Prop) (f : A -> B) (a : A) : (term78 A B P f a) = ((term78 A B P f a) = True).
Proof. exact (@lem7 (term78 A B P f a)). Qed.
Lemma lem5808042 {A : Type'} (t : A -> Prop) (h1 : t = (@EMPTY A)) : t = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem5808043 {A : Type'} (a : A) : (@INSERT A a) = (@INSERT A a).
Proof. exact (eq_refl (@INSERT A a)). Qed.
Lemma lem5808044 {A : Type'} (a : A) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (@INSERT A a t) = (@INSERT A a (@EMPTY A)).
Proof. exact (MK_COMB (@lem5808043 A a) (@lem5808042 A t h1)). Qed.
Lemma lem5808045 {A B : Type'} (op : type1400 B) : (@iterate B A op) = (@iterate B A op).
Proof. exact (eq_refl (@iterate B A op)). Qed.
Lemma lem5808046 {A B : Type'} (op : type1400 B) (a : A) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term184 A B op a t) = (term185 A B op a).
Proof. exact (MK_COMB (@lem5808045 A B op) (@lem5808044 A a t h1)). Qed.
Lemma lem5808047 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5808048 {A B : Type'} (op : type1400 B) (a : A) (f : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term186 A B op a t f) = (term131 A B op a f).
Proof. exact (MK_COMB (@lem5808046 A B op a t h1) (@lem5808047 A B f)). Qed.
Lemma lem5808050 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) : term187 A B op f x.
Proof. exact (fun h0 : @monoidal B op => @lem5807522 A B f x op h0). Qed.
Lemma lem5808051 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) : term187 A B op f x.
Proof. exact (@lem5808050 A B op f x). Qed.
Lemma lem5808052 {A B : Type'} (op : type1400 B) (f : A -> B) (a : A) : term187 A B op f a.
Proof. exact (@lem5808051 A B op f a). Qed.
Lemma lem5808054 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = True.
Proof. exact (EQ_MP (@lem5807528 B op) (@lem5807230 B op h1)). Qed.
Lemma lem5808055 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : True = (@monoidal B op).
Proof. exact (SYM (@lem5808054 B op h1)). Qed.
Lemma lem5808056 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (EQ_MP (@lem5808055 B op h1) (@lem0)). Qed.
Lemma lem5808057 {A B : Type'} (f : A -> B) (a : A) (op : type1400 B) (h1 : @monoidal B op) : (term131 A B op a f) = (f a).
Proof. exact (@lem5808052 A B op f a (@lem5808056 B op h1)). Qed.
Lemma lem5808058 {A B : Type'} (f : A -> B) (a : A) (op : type1400 B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : t = (@EMPTY A)) : (term186 A B op a t f) = (f a).
Proof. exact (TRANS (@lem5808048 A B op a f t h2) (@lem5808057 A B f a op h1)). Qed.
Lemma lem5808059 {B : Type'} (P : B -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem5808060 {A B : Type'} (P : B -> Prop) (f : A -> B) (a : A) (op : type1400 B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : t = (@EMPTY A)) : (term115 A B P op a t f) = (term78 A B P f a).
Proof. exact (MK_COMB (@lem5808059 B P) (@lem5808058 A B f a op t h1 h2)). Qed.
Lemma lem5808062 {A B : Type'} (a : A) (P : B -> Prop) (f : A -> B) (h1 : term181 A B a P f) : (term78 A B P f a) = True.
Proof. exact (EQ_MP (@lem5808039 A B P f a) (@lem5808038 A B a P f h1)). Qed.
Lemma lem5808063 {A B : Type'} (op : type1400 B) (a : A) (P : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term181 A B a P f) (h3 : t = (@EMPTY A)) : (term115 A B P op a t f) = True.
Proof. exact (TRANS (@lem5808060 A B P f a op t h1 h3) (@lem5808062 A B a P f h2)). Qed.
Lemma lem5808064 {A B : Type'} (P : B -> Prop) (a : A) (f : A -> B) (op : type1400 B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : t = (@EMPTY A)) : term188 A B P op a t f.
Proof. exact (fun h0 : term181 A B a P f => @lem5808063 A B op a P f t h1 h0 h2). Qed.
Lemma lem5808065 {A B : Type'} (op : type1400 B) (a : A) (P : B -> Prop) (f : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : term189 A B op t a P f.
Proof. exact (@lem5808023 A B op a P f True t h1). Qed.
Lemma lem5808066 {A B : Type'} (a : A) (P : B -> Prop) (f : A -> B) (op : type1400 B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : t = (@EMPTY A)) : (term117 A B P op a t f) = (term190 A B a P f).
Proof. exact (@lem5808065 A B op a P f t h2 (@lem5808064 A B P a f op t h1 h2)). Qed.
Lemma lem5808068 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5808069 {A B : Type'} (a : A) (P : B -> Prop) (f : A -> B) : (term190 A B a P f) = True.
Proof. exact (@lem5808068 (term181 A B a P f)). Qed.
Lemma lem5808070 {A B : Type'} (P : B -> Prop) (a : A) (f : A -> B) (op : type1400 B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : t = (@EMPTY A)) : (term117 A B P op a t f) = True.
Proof. exact (TRANS (@lem5808066 A B a P f op t h1 h2) (@lem5808069 A B a P f)). Qed.
Lemma lem5808071 {A B : Type'} (P : B -> Prop) (a : A) (f : A -> B) (op : type1400 B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : t = (@EMPTY A)) : term191 A B P op a t f.
Proof. exact (fun h0 : term172 A a => @lem5808070 A B P a f op t h1 h2). Qed.
Lemma lem5808072 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : t = (@EMPTY A)) : term192 A B P op t f a.
Proof. exact (@lem5807862 A B P op f a True t h1). Qed.
Lemma lem5808073 {A B : Type'} (P : B -> Prop) (f : A -> B) (a : A) (op : type1400 B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : t = (@EMPTY A)) : (term119 A B P op a t f) = (term193 A a).
Proof. exact (@lem5808072 A B P op f a t h2 (@lem5808071 A B P a f op t h1 h2)). Qed.
Lemma lem5808075 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5808076 {A : Type'} (a : A) : (term193 A a) = True.
Proof. exact (@lem5808075 (term172 A a)). Qed.
Lemma lem5808077 {A B : Type'} (P : B -> Prop) (a : A) (f : A -> B) (op : type1400 B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : t = (@EMPTY A)) : (term119 A B P op a t f) = True.
Proof. exact (TRANS (@lem5808073 A B P f a op t h1 h2) (@lem5808076 A a)). Qed.
Lemma lem5808078 {A B : Type'} (P : B -> Prop) (a : A) (f : A -> B) (op : type1400 B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : t = (@EMPTY A)) : True = (term119 A B P op a t f).
Proof. exact (SYM (@lem5808077 A B P a f op t h1 h2)). Qed.
Lemma lem5808079 {A B : Type'} (P : B -> Prop) (a : A) (f : A -> B) (op : type1400 B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : t = (@EMPTY A)) : term119 A B P op a t f.
Proof. exact (EQ_MP (@lem5808078 A B P a f op t h1 h2) (@lem0)). Qed.
Lemma lem5808113 {A : Type'} (t : A -> Prop) : term194 A t.
Proof. exact (@lem82 (t = (@EMPTY A))). Qed.
Lemma lem5808129 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term132 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5808130 (p : Prop) (q : Prop) (p' : Prop) : term133 p q p'.
Proof. exact (fun q' : Prop => @lem5808129 p q p' q'). Qed.
Lemma lem5808131 (p : Prop) (q : Prop) : term134 p q.
Proof. exact (fun p' : Prop => @lem5808130 p q p'). Qed.
Lemma lem5808132 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) : term135 A B P op a t f.
Proof. exact (@lem5808131 (term52 A B P op f a t) (term117 A B P op a t f)). Qed.
Lemma lem5808133 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) (p' : Prop) : term136 A B P op a t f p'.
Proof. exact (@lem5808132 A B P op a t f p'). Qed.
Lemma lem5808134 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) (p' : Prop) : (term136 A B P op a t f p') = (term137 A B P op a t f p').
Proof. exact (eq_refl (term136 A B P op a t f p')). Qed.
Lemma lem5808135 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) (p' : Prop) : term137 A B P op a t f p'.
Proof. exact (EQ_MP (@lem5808134 A B P op a t f p') (@lem5808133 A B P op a t f p')). Qed.
Lemma lem5808136 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term138 A B P op a t f p' q'.
Proof. exact (@lem5808135 A B P op a t f p' q'). Qed.
Lemma lem5808137 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : (term138 A B P op a t f p' q') = (term139 A B P op a t f p' q').
Proof. exact (eq_refl (term138 A B P op a t f p' q')). Qed.
Lemma lem5808138 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term139 A B P op a t f p' q'.
Proof. exact (EQ_MP (@lem5808137 A B P op a t f p' q') (@lem5808136 A B P op a t f p' q')). Qed.
Lemma lem5808144 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term132 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5808145 (p : Prop) (q : Prop) (p' : Prop) : term133 p q p'.
Proof. exact (fun q' : Prop => @lem5808144 p q p' q'). Qed.
Lemma lem5808146 (p : Prop) (q : Prop) : term134 p q.
Proof. exact (fun p' : Prop => @lem5808145 p q p'). Qed.
Lemma lem5808147 {A B : Type'} (P : B -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) : term140 A B P op t f.
Proof. exact (@lem5808146 (term2 A t) (term141 A B P op t f)). Qed.
Lemma lem5808148 {A B : Type'} (P : B -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) (p' : Prop) : term142 A B P op t f p'.
Proof. exact (@lem5808147 A B P op t f p'). Qed.
Lemma lem5808149 {A B : Type'} (P : B -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) (p' : Prop) : (term142 A B P op t f p') = (term143 A B P op t f p').
Proof. exact (eq_refl (term142 A B P op t f p')). Qed.
Lemma lem5808150 {A B : Type'} (P : B -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) (p' : Prop) : term143 A B P op t f p'.
Proof. exact (EQ_MP (@lem5808149 A B P op t f p') (@lem5808148 A B P op t f p')). Qed.
Lemma lem5808151 {A B : Type'} (P : B -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term144 A B P op t f p' q'.
Proof. exact (@lem5808150 A B P op t f p' q'). Qed.
Lemma lem5808152 {A B : Type'} (P : B -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : (term144 A B P op t f p' q') = (term145 A B P op t f p' q').
Proof. exact (eq_refl (term144 A B P op t f p' q')). Qed.
Lemma lem5808153 {A B : Type'} (P : B -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term145 A B P op t f p' q'.
Proof. exact (EQ_MP (@lem5808152 A B P op t f p' q') (@lem5808151 A B P op t f p' q')). Qed.
Lemma lem5808155 {A : Type'} (t : A -> Prop) (h1 : term2 A t) : (t = (@EMPTY A)) = False.
Proof. exact (@lem5808113 A t (@lem5807180 A t h1)). Qed.
Lemma lem5808156 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5808157 {A : Type'} (t : A -> Prop) (h1 : term2 A t) : (term2 A t) = (~ False).
Proof. exact (MK_COMB (@lem5808156) (@lem5808155 A t h1)). Qed.
Lemma lem5808159 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5808160 {A : Type'} (t : A -> Prop) (h1 : term2 A t) : (term2 A t) = True.
Proof. exact (TRANS (@lem5808157 A t h1) (@lem5808159)). Qed.
Lemma lem5808161 {A B : Type'} (P : B -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) (q' : Prop) : term195 A B P op t f q'.
Proof. exact (@lem5808153 A B P op t f True q'). Qed.
Lemma lem5808162 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (q' : Prop) (t : A -> Prop) (h1 : term2 A t) : term196 A B P op t f q'.
Proof. exact (@lem5808161 A B P op t f q' (@lem5808160 A t h1)). Qed.
Lemma lem5808255 {A B : Type'} (P : B -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) : (term141 A B P op t f) = (term141 A B P op t f).
Proof. exact (eq_refl (term141 A B P op t f)). Qed.
Lemma lem5808256 {A B : Type'} (P : B -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) : term197 A B P op t f.
Proof. exact (fun h0 : True => @lem5808255 A B P op t f). Qed.
Lemma lem5808257 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : term2 A t) : term198 A B P op t f.
Proof. exact (@lem5808162 A B P op f (term141 A B P op t f) t h1). Qed.
Lemma lem5808258 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : term2 A t) : (term33 A B P op t f) = (term199 A B P op t f).
Proof. exact (@lem5808257 A B P op f t h1 (@lem5808256 A B P op t f)). Qed.
Lemma lem5808260 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem5808261 {A B : Type'} (P : B -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) : (term199 A B P op t f) = (term141 A B P op t f).
Proof. exact (@lem5808260 (term141 A B P op t f)). Qed.
Lemma lem5808349 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : term2 A t) : (term33 A B P op t f) = (term141 A B P op t f).
Proof. exact (TRANS (@lem5808258 A B P op f t h1) (@lem5808261 A B P op t f)). Qed.
Lemma lem5808350 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5808351 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : term2 A t) : (term49 A B P op t f) = (term200 A B P op t f).
Proof. exact (MK_COMB (@lem5808350) (@lem5808349 A B P op f t h1)). Qed.
Lemma lem5808441 {A : Type'} (a : A) (t : A -> Prop) : (term50 A a t) = (term50 A a t).
Proof. exact (eq_refl (term50 A a t)). Qed.
Lemma lem5808442 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : term2 A t) : (term52 A B P op f a t) = (term201 A B P op f a t).
Proof. exact (MK_COMB (@lem5808351 A B P op f t h1) (@lem5808441 A a t)). Qed.
Lemma lem5808534 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (q' : Prop) : term202 A B P op f a t q'.
Proof. exact (@lem5808138 A B P op a t f (term201 A B P op f a t) q'). Qed.
Lemma lem5808535 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (q' : Prop) (t : A -> Prop) (h1 : term2 A t) : term203 A B P op f a t q'.
Proof. exact (@lem5808534 A B P op f a t q' (@lem5808442 A B P op f a t h1)). Qed.
Lemma lem5808649 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) : (term117 A B P op a t f) = (term117 A B P op a t f).
Proof. exact (eq_refl (term117 A B P op a t f)). Qed.
Lemma lem5808650 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) : term204 A B P op a t f.
Proof. exact (fun h0 : term201 A B P op f a t => @lem5808649 A B P op a t f). Qed.
Lemma lem5808651 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (f : A -> B) (t : A -> Prop) (h1 : term2 A t) : term205 A B P op a t f.
Proof. exact (@lem5808535 A B P op f a (term117 A B P op a t f) t h1). Qed.
Lemma lem5808652 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (f : A -> B) (t : A -> Prop) (h1 : term2 A t) : (term119 A B P op a t f) = (term206 A B P op a t f).
Proof. exact (@lem5808651 A B P op a f t h1 (@lem5808650 A B P op a t f)). Qed.
Lemma lem5809063 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (f : A -> B) (t : A -> Prop) (h1 : term2 A t) : (term206 A B P op a t f) = (term119 A B P op a t f).
Proof. exact (SYM (@lem5808652 A B P op a f t h1)). Qed.
Lemma lem5809064 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term207 _120477 _120519 _120521 op.
Proof. exact (@lem5753565 _120477 _120519 _120521 op). Qed.
Lemma lem5809065 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term207 _120477 _120519 _120521 op) = (term208 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term207 _120477 _120519 _120521 op)). Qed.
Lemma lem5809066 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term208 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem5809065 _120477 _120519 _120521 op) (@lem5809064 _120477 _120519 _120521 op)). Qed.
Lemma lem5809067 {_120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : @monoidal _120519 op.
Proof. exact (h1). Qed.
Lemma lem5809068 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term209 _120477 _120519 _120521 op.
Proof. exact (@lem5809066 _120477 _120519 _120521 op (@lem5809067 _120519 op h1)). Qed.
Lemma lem5809069 {_120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term210 _120519 _120521 op.
Proof. exact (proj2 (@lem5809068 Prop _120519 _120521 op h1)). Qed.
Lemma lem5809070 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term211 _120519 _120521 op f.
Proof. exact (@lem5809069 _120519 _120521 op h1 f). Qed.
Lemma lem5809071 {_120519 _120521 : Type'} (op : type1400 _120519) (f : _120521 -> _120519) : (term211 _120519 _120521 op f) = (term212 _120519 _120521 op f).
Proof. exact (eq_refl (term211 _120519 _120521 op f)). Qed.
Lemma lem5809072 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term212 _120519 _120521 op f.
Proof. exact (EQ_MP (@lem5809071 _120519 _120521 op f) (@lem5809070 _120519 _120521 f op h1)). Qed.
Lemma lem5809073 {_120519 _120521 : Type'} (f : _120521 -> _120519) (x : _120521) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term213 _120519 _120521 op f x.
Proof. exact (@lem5809072 _120519 _120521 f op h1 x). Qed.
Lemma lem5809074 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) : (term213 _120519 _120521 op f x) = (term214 _120519 _120521 x op f).
Proof. exact (eq_refl (term213 _120519 _120521 op f x)). Qed.
Lemma lem5809075 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term214 _120519 _120521 x op f.
Proof. exact (EQ_MP (@lem5809074 _120519 _120521 x op f) (@lem5809073 _120519 _120521 f x op h1)). Qed.
Lemma lem5809076 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term215 _120519 _120521 x op f s.
Proof. exact (@lem5809075 _120519 _120521 x f op h1 s). Qed.
Lemma lem5809077 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term215 _120519 _120521 x op f s) = (term216 _120519 _120521 x op s f).
Proof. exact (eq_refl (term215 _120519 _120521 x op f s)). Qed.
Lemma lem5809078 {_120519 _120521 : Type'} (x : _120521) (s : _120521 -> Prop) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term216 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem5809077 _120519 _120521 x op s f) (@lem5809076 _120519 _120521 x f s op h1)). Qed.
Lemma lem5809079 {_120521 : Type'} (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : @FINITE _120521 s.
Proof. exact (h1). Qed.
Lemma lem5809080 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @FINITE _120521 s) (h2 : @monoidal _120519 op) : (term217 _120519 _120521 op x s f) = (term218 _120519 _120521 x op s f).
Proof. exact (@lem5809078 _120519 _120521 x s f op h2 (@lem5809079 _120521 s h1)). Qed.
Lemma lem5809081 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : term219 _120519 _120521 x op s f.
Proof. exact (fun h0 : @monoidal _120519 op => @lem5809080 _120519 _120521 x f s op h1 h0). Qed.
Lemma lem5809082 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term220 _120519 _120521 x op s f.
Proof. exact (fun h0 : @FINITE _120521 s => @lem5809081 _120519 _120521 x op f s h0). Qed.
Lemma lem5809084 (p : Prop) (q : Prop) (r : Prop) : (term27 p q r) = (term26 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem5809089 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term220 _120519 _120521 x op s f) = (term221 _120519 _120521 x op s f).
Proof. exact (@lem5809084 (@FINITE _120521 s) (@monoidal _120519 op) ((term217 _120519 _120521 op x s f) = (term218 _120519 _120521 x op s f))). Qed.
Lemma lem5809100 {B : Type'} (op : type1400 B) : (@monoidal B op) = ((@monoidal B op) = True).
Proof. exact (@lem7 (@monoidal B op)). Qed.
Lemma lem5809102 {B : Type'} (x : B) (P : B -> Prop) (op : type1400 B) (h1 : term25 B P op) : term222 B P op x.
Proof. exact (@lem5807231 B P op h1 x). Qed.
Lemma lem5809103 {B : Type'} (P : B -> Prop) (op : type1400 B) (x : B) : (term222 B P op x) = (term223 B P op x).
Proof. exact (eq_refl (term222 B P op x)). Qed.
Lemma lem5809104 {B : Type'} (x : B) (P : B -> Prop) (op : type1400 B) (h1 : term25 B P op) : term223 B P op x.
Proof. exact (EQ_MP (@lem5809103 B P op x) (@lem5809102 B x P op h1)). Qed.
Lemma lem5809105 {B : Type'} (x : B) (y : B) (P : B -> Prop) (op : type1400 B) (h1 : term25 B P op) : term224 B P op x y.
Proof. exact (@lem5809104 B x P op h1 y). Qed.
Lemma lem5809106 {B : Type'} (P : B -> Prop) (op : type1400 B) (x : B) (y : B) : (term224 B P op x y) = (term225 B P op x y).
Proof. exact (eq_refl (term224 B P op x y)). Qed.
Lemma lem5809107 {B : Type'} (x : B) (y : B) (P : B -> Prop) (op : type1400 B) (h1 : term25 B P op) : term225 B P op x y.
Proof. exact (EQ_MP (@lem5809106 B P op x y) (@lem5809105 B x y P op h1)). Qed.
Lemma lem5809108 {B : Type'} (x : B) (P : B -> Prop) (y : B) (h1 : term226 B x P y) : term226 B x P y.
Proof. exact (h1). Qed.
Lemma lem5809109 {B : Type'} (op : type1400 B) (x : B) (P : B -> Prop) (y : B) (h1 : term25 B P op) (h2 : term226 B x P y) : term227 B P op x y.
Proof. exact (@lem5809107 B x y P op h1 (@lem5809108 B x P y h2)). Qed.
Lemma lem5809110 {B : Type'} (P : B -> Prop) (op : type1400 B) (x : B) (y : B) : (term227 B P op x y) = ((term227 B P op x y) = True).
Proof. exact (@lem7 (term227 B P op x y)). Qed.
Lemma lem5809111 {B : Type'} (op : type1400 B) (x : B) (P : B -> Prop) (y : B) (h1 : term25 B P op) (h2 : term226 B x P y) : (term227 B P op x y) = True.
Proof. exact (EQ_MP (@lem5809110 B P op x y) (@lem5809109 B op x P y h1 h2)). Qed.
Lemma lem5809133 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term132 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5809134 (p : Prop) (q : Prop) (p' : Prop) : term133 p q p'.
Proof. exact (fun q' : Prop => @lem5809133 p q p' q'). Qed.
Lemma lem5809135 (p : Prop) (q : Prop) : term134 p q.
Proof. exact (fun p' : Prop => @lem5809134 p q p'). Qed.
Lemma lem5809136 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) : term228 A B P op a t f.
Proof. exact (@lem5809135 (term201 A B P op f a t) (term117 A B P op a t f)). Qed.
Lemma lem5809137 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) (p' : Prop) : term229 A B P op a t f p'.
Proof. exact (@lem5809136 A B P op a t f p'). Qed.
Lemma lem5809138 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) (p' : Prop) : (term229 A B P op a t f p') = (term230 A B P op a t f p').
Proof. exact (eq_refl (term229 A B P op a t f p')). Qed.
Lemma lem5809139 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) (p' : Prop) : term230 A B P op a t f p'.
Proof. exact (EQ_MP (@lem5809138 A B P op a t f p') (@lem5809137 A B P op a t f p')). Qed.
Lemma lem5809140 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term231 A B P op a t f p' q'.
Proof. exact (@lem5809139 A B P op a t f p' q'). Qed.
Lemma lem5809141 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : (term231 A B P op a t f p' q') = (term232 A B P op a t f p' q').
Proof. exact (eq_refl (term231 A B P op a t f p' q')). Qed.
Lemma lem5809142 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term232 A B P op a t f p' q'.
Proof. exact (EQ_MP (@lem5809141 A B P op a t f p' q') (@lem5809140 A B P op a t f p' q')). Qed.
Lemma lem5809234 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) : (term201 A B P op f a t) = (term201 A B P op f a t).
Proof. exact (eq_refl (term201 A B P op f a t)). Qed.
Lemma lem5809235 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (q' : Prop) : term233 A B P op f a t q'.
Proof. exact (@lem5809142 A B P op a t f (term201 A B P op f a t) q'). Qed.
Lemma lem5809236 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (q' : Prop) : term234 A B P op f a t q'.
Proof. exact (@lem5809235 A B P op f a t q' (@lem5809234 A B P op f a t)). Qed.
Lemma lem5809237 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : term201 A B P op f a t) : term201 A B P op f a t.
Proof. exact (h1). Qed.
Lemma lem5809238 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : term201 A B P op f a t) : term50 A a t.
Proof. exact (proj2 (@lem5809237 A B P op f a t h1)). Qed.
Lemma lem5809239 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : term201 A B P op f a t) : @FINITE A t.
Proof. exact (proj2 (@lem5809238 A B P op f a t h1)). Qed.
Lemma lem5809240 {A : Type'} (t : A -> Prop) : (@FINITE A t) = ((@FINITE A t) = True).
Proof. exact (@lem7 (@FINITE A t)). Qed.
Lemma lem5809242 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : term201 A B P op f a t) : term169 A a t.
Proof. exact (proj1 (@lem5809238 A B P op f a t h1)). Qed.
Lemma lem5809243 {A : Type'} (a : A) (t : A -> Prop) : term235 A a t.
Proof. exact (@lem82 (@IN A a t)). Qed.
Lemma lem5809245 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : term201 A B P op f a t) : term141 A B P op t f.
Proof. exact (proj1 (@lem5809237 A B P op f a t h1)). Qed.
Lemma lem5809246 {A B : Type'} (t : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term34 A B t P f) : term34 A B t P f.
Proof. exact (h1). Qed.
Lemma lem5809247 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : term34 A B t P f) (h2 : term201 A B P op f a t) : term31 A B P op t f.
Proof. exact (@lem5809245 A B P op f a t h2 (@lem5809246 A B t P f h1)). Qed.
Lemma lem5809248 {A B : Type'} (P : B -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) : (term31 A B P op t f) = ((term31 A B P op t f) = True).
Proof. exact (@lem7 (term31 A B P op t f)). Qed.
Lemma lem5809249 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : term34 A B t P f) (h2 : term201 A B P op f a t) : (term31 A B P op t f) = True.
Proof. exact (EQ_MP (@lem5809248 A B P op t f) (@lem5809247 A B P op f a t h1 h2)). Qed.
Lemma lem5809258 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term132 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5809259 (p : Prop) (q : Prop) (p' : Prop) : term133 p q p'.
Proof. exact (fun q' : Prop => @lem5809258 p q p' q'). Qed.
Lemma lem5809260 (p : Prop) (q : Prop) : term134 p q.
Proof. exact (fun p' : Prop => @lem5809259 p q p'). Qed.
Lemma lem5809261 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) : term176 A B P op a t f.
Proof. exact (@lem5809260 (term112 A B a t P f) (term115 A B P op a t f)). Qed.
Lemma lem5809262 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) (p' : Prop) : term177 A B P op a t f p'.
Proof. exact (@lem5809261 A B P op a t f p'). Qed.
Lemma lem5809263 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) (p' : Prop) : (term177 A B P op a t f p') = (term178 A B P op a t f p').
Proof. exact (eq_refl (term177 A B P op a t f p')). Qed.
Lemma lem5809264 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) (p' : Prop) : term178 A B P op a t f p'.
Proof. exact (EQ_MP (@lem5809263 A B P op a t f p') (@lem5809262 A B P op a t f p')). Qed.
Lemma lem5809265 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term179 A B P op a t f p' q'.
Proof. exact (@lem5809264 A B P op a t f p' q'). Qed.
Lemma lem5809266 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : (term179 A B P op a t f p' q') = (term180 A B P op a t f p' q').
Proof. exact (eq_refl (term179 A B P op a t f p' q')). Qed.
Lemma lem5809267 {A B : Type'} (P : B -> Prop) (op : type1400 B) (a : A) (t : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term180 A B P op a t f p' q'.
Proof. exact (EQ_MP (@lem5809266 A B P op a t f p' q') (@lem5809265 A B P op a t f p' q')). Qed.
Lemma lem5809297 {A B : Type'} (a : A) (t : A -> Prop) (P : B -> Prop) (f : A -> B) : (term112 A B a t P f) = (term112 A B a t P f).
Proof. exact (eq_refl (term112 A B a t P f)). Qed.
Lemma lem5809298 {A B : Type'} (op : type1400 B) (a : A) (t : A -> Prop) (P : B -> Prop) (f : A -> B) (q' : Prop) : term236 A B op a t P f q'.
Proof. exact (@lem5809267 A B P op a t f (term112 A B a t P f) q'). Qed.
Lemma lem5809299 {A B : Type'} (op : type1400 B) (a : A) (t : A -> Prop) (P : B -> Prop) (f : A -> B) (q' : Prop) : term237 A B op a t P f q'.
Proof. exact (@lem5809298 A B op a t P f q' (@lem5809297 A B a t P f)). Qed.
Lemma lem5809300 {A B : Type'} (a : A) (t : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term112 A B a t P f) : term112 A B a t P f.
Proof. exact (h1). Qed.
Lemma lem5809301 {A B : Type'} (a : A) (t : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term112 A B a t P f) : term34 A B t P f.
Proof. exact (proj2 (@lem5809300 A B a t P f h1)). Qed.
Lemma lem5809302 {A B : Type'} (x' : A) (a : A) (t : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term112 A B a t P f) : term238 A B t P f x'.
Proof. exact (@lem5809301 A B a t P f h1 x'). Qed.
Lemma lem5809303 {A B : Type'} (t : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) : (term238 A B t P f x') = (term108 A B t P f x').
Proof. exact (eq_refl (term238 A B t P f x')). Qed.
Lemma lem5809304 {A B : Type'} (x' : A) (a : A) (t : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term112 A B a t P f) : term108 A B t P f x'.
Proof. exact (EQ_MP (@lem5809303 A B t P f x') (@lem5809302 A B x' a t P f h1)). Qed.
Lemma lem5809305 {A : Type'} (x' : A) (t : A -> Prop) (h1 : @IN A x' t) : @IN A x' t.
Proof. exact (h1). Qed.
Lemma lem5809306 {A B : Type'} (a : A) (P : B -> Prop) (f : A -> B) (x' : A) (t : A -> Prop) (h1 : term112 A B a t P f) (h2 : @IN A x' t) : term78 A B P f x'.
Proof. exact (@lem5809304 A B x' a t P f h1 (@lem5809305 A x' t h2)). Qed.
Lemma lem5809307 {A B : Type'} (P : B -> Prop) (f : A -> B) (x' : A) : (term78 A B P f x') = ((term78 A B P f x') = True).
Proof. exact (@lem7 (term78 A B P f x')). Qed.
Lemma lem5809308 {A B : Type'} (a : A) (P : B -> Prop) (f : A -> B) (x' : A) (t : A -> Prop) (h1 : term112 A B a t P f) (h2 : @IN A x' t) : (term78 A B P f x') = True.
Proof. exact (EQ_MP (@lem5809307 A B P f x') (@lem5809306 A B a P f x' t h1 h2)). Qed.
Lemma lem5809314 {A B : Type'} (a : A) (t : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term112 A B a t P f) : term78 A B P f a.
Proof. exact (proj1 (@lem5809300 A B a t P f h1)). Qed.
Lemma lem5809315 {A B : Type'} (P : B -> Prop) (f : A -> B) (a : A) : (term78 A B P f a) = ((term78 A B P f a) = True).
Proof. exact (@lem7 (term78 A B P f a)). Qed.
Lemma lem5809318 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term221 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem5809089 _120519 _120521 x op s f) (@lem5809082 _120519 _120521 x op s f)). Qed.
Lemma lem5809319 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term239 A B x op s f.
Proof. exact (@lem5809318 B A x op s f). Qed.
Lemma lem5809320 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) : term239 A B a op t f.
Proof. exact (@lem5809319 A B a op t f). Qed.
Lemma lem5809324 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : term201 A B P op f a t) : (@FINITE A t) = True.
Proof. exact (EQ_MP (@lem5809240 A t) (@lem5809239 A B P op f a t h1)). Qed.
Lemma lem5809325 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5809326 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : term201 A B P op f a t) : (term240 A t) = (and True).
Proof. exact (MK_COMB (@lem5809325) (@lem5809324 A B P op f a t h1)). Qed.
Lemma lem5809328 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = True.
Proof. exact (EQ_MP (@lem5809100 B op) (@lem5807230 B op h1)). Qed.
Lemma lem5809329 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term201 A B P op f a t) : (term241 A B t op) = (True /\ True).
Proof. exact (MK_COMB (@lem5809326 A B P op f a t h2) (@lem5809328 B op h1)). Qed.
Lemma lem5809331 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5809332 : (True /\ True) = True.
Proof. exact (@lem5809331 True). Qed.
Lemma lem5809333 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term201 A B P op f a t) : (term241 A B t op) = True.
Proof. exact (TRANS (@lem5809329 A B P op f a t h1 h2) (@lem5809332)). Qed.
Lemma lem5809334 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term201 A B P op f a t) : True = (term241 A B t op).
Proof. exact (SYM (@lem5809333 A B P op f a t h1 h2)). Qed.
Lemma lem5809335 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term201 A B P op f a t) : term241 A B t op.
Proof. exact (EQ_MP (@lem5809334 A B P op f a t h1 h2) (@lem0)). Qed.
Lemma lem5809336 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term201 A B P op f a t) : (term186 A B op a t f) = (term242 A B a op t f).
Proof. exact (@lem5809320 A B a op t f (@lem5809335 A B P op f a t h1 h2)). Qed.
Lemma lem5809338 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term243 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem5809339 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term244 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem5809338 _2963 g t e g' t' e'). Qed.
Lemma lem5809340 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term245 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem5809339 _2963 g t e g' t'). Qed.
Lemma lem5809341 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term246 _2963 g t e.
Proof. exact (fun g' : Prop => @lem5809340 _2963 g t e g'). Qed.
Lemma lem5809342 {B : Type'} (g : Prop) (t : B) (e : B) : term246 B g t e.
Proof. exact (@lem5809341 B g t e). Qed.
Lemma lem5809343 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) : term247 A B a op t f.
Proof. exact (@lem5809342 B (@IN A a t) (@iterate B A op t f) (term248 A B a op t f)). Qed.
Lemma lem5809344 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g' : Prop) : term249 A B a op t f g'.
Proof. exact (@lem5809343 A B a op t f g'). Qed.
Lemma lem5809345 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g' : Prop) : (term249 A B a op t f g') = (term250 A B a op t f g').
Proof. exact (eq_refl (term249 A B a op t f g')). Qed.
Lemma lem5809346 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g' : Prop) : term250 A B a op t f g'.
Proof. exact (EQ_MP (@lem5809345 A B a op t f g') (@lem5809344 A B a op t f g')). Qed.
Lemma lem5809347 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g' : Prop) (t' : B) : term251 A B a op t f g' t'.
Proof. exact (@lem5809346 A B a op t f g' t'). Qed.
Lemma lem5809348 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g' : Prop) (t' : B) : (term251 A B a op t f g' t') = (term252 A B a op t f g' t').
Proof. exact (eq_refl (term251 A B a op t f g' t')). Qed.
Lemma lem5809349 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g' : Prop) (t' : B) : term252 A B a op t f g' t'.
Proof. exact (EQ_MP (@lem5809348 A B a op t f g' t') (@lem5809347 A B a op t f g' t')). Qed.
Lemma lem5809350 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g' : Prop) (t' : B) (e' : B) : term253 A B a op t f g' t' e'.
Proof. exact (@lem5809349 A B a op t f g' t' e'). Qed.
Lemma lem5809351 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g' : Prop) (t' : B) (e' : B) : (term253 A B a op t f g' t' e') = (term254 A B a op t f g' t' e').
Proof. exact (eq_refl (term253 A B a op t f g' t' e')). Qed.
Lemma lem5809352 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g' : Prop) (t' : B) (e' : B) : term254 A B a op t f g' t' e'.
Proof. exact (EQ_MP (@lem5809351 A B a op t f g' t' e') (@lem5809350 A B a op t f g' t' e')). Qed.
Lemma lem5809354 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : term201 A B P op f a t) : (@IN A a t) = False.
Proof. exact (@lem5809243 A a t (@lem5809242 A B P op f a t h1)). Qed.
Lemma lem5809355 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (t' : B) (e' : B) : term255 A B a op t f t' e'.
Proof. exact (@lem5809352 A B a op t f False t' e'). Qed.
Lemma lem5809356 {A B : Type'} (t' : B) (e' : B) (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : term201 A B P op f a t) : term256 A B a op t f t' e'.
Proof. exact (@lem5809355 A B a op t f t' e' (@lem5809354 A B P op f a t h1)). Qed.
Lemma lem5809360 {A B : Type'} (op : type1400 B) (t : A -> Prop) (f : A -> B) : (@iterate B A op t f) = (@iterate B A op t f).
Proof. exact (eq_refl (@iterate B A op t f)). Qed.
Lemma lem5809361 {A B : Type'} (op : type1400 B) (t : A -> Prop) (f : A -> B) : term257 A B op t f.
Proof. exact (fun h0 : False => @lem5809360 A B op t f). Qed.
Lemma lem5809362 {A B : Type'} (e' : B) (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : term201 A B P op f a t) : term258 A B a op t f e'.
Proof. exact (@lem5809356 A B (@iterate B A op t f) e' P op f a t h1). Qed.
Lemma lem5809363 {A B : Type'} (e' : B) (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : term201 A B P op f a t) : term259 A B a op t f e'.
Proof. exact (@lem5809362 A B e' P op f a t h1 (@lem5809361 A B op t f)). Qed.
Lemma lem5809369 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) : (term248 A B a op t f) = (term248 A B a op t f).
Proof. exact (eq_refl (term248 A B a op t f)). Qed.
Lemma lem5809370 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) : term260 A B a op t f.
Proof. exact (fun h0 : ~ False => @lem5809369 A B a op t f). Qed.
Lemma lem5809371 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : term201 A B P op f a t) : term261 A B a op t f.
Proof. exact (@lem5809363 A B (term248 A B a op t f) P op f a t h1). Qed.
Lemma lem5809372 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : term201 A B P op f a t) : (term242 A B a op t f) = (term262 A B a op t f).
Proof. exact (@lem5809371 A B P op f a t h1 (@lem5809370 A B a op t f)). Qed.
Lemma lem5809374 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5809375 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem5809374 B t1 t2). Qed.
Lemma lem5809376 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) : (term262 A B a op t f) = (term248 A B a op t f).
Proof. exact (@lem5809375 B (@iterate B A op t f) (term248 A B a op t f)). Qed.
Lemma lem5809377 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : term201 A B P op f a t) : (term242 A B a op t f) = (term248 A B a op t f).
Proof. exact (TRANS (@lem5809372 A B P op f a t h1) (@lem5809376 A B a op t f)). Qed.
Lemma lem5809378 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term201 A B P op f a t) : (term186 A B op a t f) = (term248 A B a op t f).
Proof. exact (TRANS (@lem5809336 A B P op f a t h1 h2) (@lem5809377 A B P op f a t h2)). Qed.
Lemma lem5809379 {B : Type'} (P : B -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem5809380 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term201 A B P op f a t) : (term115 A B P op a t f) = (term263 A B P a op t f).
Proof. exact (MK_COMB (@lem5809379 B P) (@lem5809378 A B P op f a t h1 h2)). Qed.
Lemma lem5809382 {B : Type'} (x : B) (y : B) (P : B -> Prop) (op : type1400 B) (h1 : term25 B P op) : term264 B P op x y.
Proof. exact (fun h0 : term226 B x P y => @lem5809111 B op x P y h1 h0). Qed.
Lemma lem5809383 {B : Type'} (x : B) (y : B) (P : B -> Prop) (op : type1400 B) (h1 : term25 B P op) : term264 B P op x y.
Proof. exact (@lem5809382 B x y P op h1). Qed.
Lemma lem5809384 {A B : Type'} (a : A) (t : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term25 B P op) : term265 A B P a op t f.
Proof. exact (@lem5809383 B (f a) (@iterate B A op t f) P op h1). Qed.
Lemma lem5809388 {A B : Type'} (a : A) (t : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term112 A B a t P f) : (term78 A B P f a) = True.
Proof. exact (EQ_MP (@lem5809315 A B P f a) (@lem5809314 A B a t P f h1)). Qed.
Lemma lem5809389 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5809390 {A B : Type'} (a : A) (t : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term112 A B a t P f) : (term105 A B P f a) = (and True).
Proof. exact (MK_COMB (@lem5809389) (@lem5809388 A B a t P f h1)). Qed.
Lemma lem5809392 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : term201 A B P op f a t) : term266 A B P op t f.
Proof. exact (fun h0 : term34 A B t P f => @lem5809249 A B P op f a t h0 h1). Qed.
Lemma lem5809400 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term132 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5809401 (p : Prop) (q : Prop) (p' : Prop) : term133 p q p'.
Proof. exact (fun q' : Prop => @lem5809400 p q p' q'). Qed.
Lemma lem5809402 (p : Prop) (q : Prop) : term134 p q.
Proof. exact (fun p' : Prop => @lem5809401 p q p'). Qed.
Lemma lem5809403 {A B : Type'} (t : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : term153 A B t P f x.
Proof. exact (@lem5809402 (@IN A x t) (term78 A B P f x)). Qed.
Lemma lem5809404 {A B : Type'} (t : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) (p' : Prop) : term154 A B t P f x p'.
Proof. exact (@lem5809403 A B t P f x p'). Qed.
Lemma lem5809405 {A B : Type'} (t : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) (p' : Prop) : (term154 A B t P f x p') = (term155 A B t P f x p').
Proof. exact (eq_refl (term154 A B t P f x p')). Qed.
Lemma lem5809406 {A B : Type'} (t : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) (p' : Prop) : term155 A B t P f x p'.
Proof. exact (EQ_MP (@lem5809405 A B t P f x p') (@lem5809404 A B t P f x p')). Qed.
Lemma lem5809407 {A B : Type'} (t : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) (p' : Prop) (q' : Prop) : term156 A B t P f x p' q'.
Proof. exact (@lem5809406 A B t P f x p' q'). Qed.
Lemma lem5809408 {A B : Type'} (t : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) (p' : Prop) (q' : Prop) : (term156 A B t P f x p' q') = (term157 A B t P f x p' q').
Proof. exact (eq_refl (term156 A B t P f x p' q')). Qed.
Lemma lem5809409 {A B : Type'} (t : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) (p' : Prop) (q' : Prop) : term157 A B t P f x p' q'.
Proof. exact (EQ_MP (@lem5809408 A B t P f x p' q') (@lem5809407 A B t P f x p' q')). Qed.
Lemma lem5809410 {A : Type'} (x : A) (t : A -> Prop) : (@IN A x t) = (@IN A x t).
Proof. exact (eq_refl (@IN A x t)). Qed.
Lemma lem5809411 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) (t : A -> Prop) (q' : Prop) : term267 A B P f x t q'.
Proof. exact (@lem5809409 A B t P f x (@IN A x t) q'). Qed.
Lemma lem5809412 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) (t : A -> Prop) (q' : Prop) : term268 A B P f x t q'.
Proof. exact (@lem5809411 A B P f x t q' (@lem5809410 A x t)). Qed.
Lemma lem5809413 {A : Type'} (x : A) (t : A -> Prop) (h1 : @IN A x t) : @IN A x t.
Proof. exact (h1). Qed.
Lemma lem5809414 {A : Type'} (x : A) (t : A -> Prop) : (@IN A x t) = ((@IN A x t) = True).
Proof. exact (@lem7 (@IN A x t)). Qed.
Lemma lem5809417 {A B : Type'} (x' : A) (a : A) (t : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term112 A B a t P f) : term269 A B t P f x'.
Proof. exact (fun h0 : @IN A x' t => @lem5809308 A B a P f x' t h1 h0). Qed.
Lemma lem5809418 {A B : Type'} (x' : A) (a : A) (t : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term112 A B a t P f) : term269 A B t P f x'.
Proof. exact (@lem5809417 A B x' a t P f h1). Qed.
Lemma lem5809419 {A B : Type'} (x : A) (a : A) (t : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term112 A B a t P f) : term269 A B t P f x.
Proof. exact (@lem5809418 A B x a t P f h1). Qed.
Lemma lem5809421 {A : Type'} (x : A) (t : A -> Prop) (h1 : @IN A x t) : (@IN A x t) = True.
Proof. exact (EQ_MP (@lem5809414 A x t) (@lem5809413 A x t h1)). Qed.
Lemma lem5809422 {A : Type'} (x : A) (t : A -> Prop) (h1 : @IN A x t) : True = (@IN A x t).
Proof. exact (SYM (@lem5809421 A x t h1)). Qed.
Lemma lem5809423 {A : Type'} (x : A) (t : A -> Prop) (h1 : @IN A x t) : @IN A x t.
Proof. exact (EQ_MP (@lem5809422 A x t h1) (@lem0)). Qed.
Lemma lem5809424 {A B : Type'} (a : A) (P : B -> Prop) (f : A -> B) (x : A) (t : A -> Prop) (h1 : term112 A B a t P f) (h2 : @IN A x t) : (term78 A B P f x) = True.
Proof. exact (@lem5809419 A B x a t P f h1 (@lem5809423 A x t h2)). Qed.
Lemma lem5809425 {A B : Type'} (x : A) (a : A) (t : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term112 A B a t P f) : term269 A B t P f x.
Proof. exact (fun h0 : @IN A x t => @lem5809424 A B a P f x t h1 h0). Qed.
Lemma lem5809426 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) (t : A -> Prop) : term270 A B P f x t.
Proof. exact (@lem5809412 A B P f x t True). Qed.
Lemma lem5809427 {A B : Type'} (x : A) (a : A) (t : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term112 A B a t P f) : (term108 A B t P f x) = (term271 A x t).
Proof. exact (@lem5809426 A B P f x t (@lem5809425 A B x a t P f h1)). Qed.
Lemma lem5809429 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5809430 {A : Type'} (x : A) (t : A -> Prop) : (term271 A x t) = True.
Proof. exact (@lem5809429 (@IN A x t)). Qed.
Lemma lem5809431 {A B : Type'} (x : A) (a : A) (t : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term112 A B a t P f) : (term108 A B t P f x) = True.
Proof. exact (TRANS (@lem5809427 A B x a t P f h1) (@lem5809430 A x t)). Qed.
Lemma lem5809432 {A B : Type'} (a : A) (t : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term112 A B a t P f) : (term110 A B t P f) = (term82 A).
Proof. exact (fun_ext (fun x : A => @lem5809431 A B x a t P f h1)). Qed.
Lemma lem5809433 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5809434 {A B : Type'} (a : A) (t : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term112 A B a t P f) : (term34 A B t P f) = (term84 A).
Proof. exact (MK_COMB (@lem5809433 A) (@lem5809432 A B a t P f h1)). Qed.
Lemma lem5809436 {A : Type'} (t : Prop) : (term85 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5809437 {A : Type'} (t : Prop) : (term85 A t) = t.
Proof. exact (@lem5809436 A t). Qed.
Lemma lem5809438 {A : Type'} : (term84 A) = True.
Proof. exact (@lem5809437 A True). Qed.
Lemma lem5809439 {A B : Type'} (a : A) (t : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term112 A B a t P f) : (term34 A B t P f) = True.
Proof. exact (TRANS (@lem5809434 A B a t P f h1) (@lem5809438 A)). Qed.
Lemma lem5809440 {A B : Type'} (a : A) (t : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term112 A B a t P f) : True = (term34 A B t P f).
Proof. exact (SYM (@lem5809439 A B a t P f h1)). Qed.
Lemma lem5809441 {A B : Type'} (a : A) (t : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term112 A B a t P f) : term34 A B t P f.
Proof. exact (EQ_MP (@lem5809440 A B a t P f h1) (@lem0)). Qed.
Lemma lem5809442 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : term112 A B a t P f) (h2 : term201 A B P op f a t) : (term31 A B P op t f) = True.
Proof. exact (@lem5809392 A B P op f a t h2 (@lem5809441 A B a t P f h1)). Qed.
Lemma lem5809443 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : term112 A B a t P f) (h2 : term201 A B P op f a t) : (term272 A B a P op t f) = (True /\ True).
Proof. exact (MK_COMB (@lem5809390 A B a t P f h1) (@lem5809442 A B P op f a t h1 h2)). Qed.
Lemma lem5809445 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5809446 : (True /\ True) = True.
Proof. exact (@lem5809445 True). Qed.
Lemma lem5809447 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : term112 A B a t P f) (h2 : term201 A B P op f a t) : (term272 A B a P op t f) = True.
Proof. exact (TRANS (@lem5809443 A B P op f a t h1 h2) (@lem5809446)). Qed.
Lemma lem5809448 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : term112 A B a t P f) (h2 : term201 A B P op f a t) : True = (term272 A B a P op t f).
Proof. exact (SYM (@lem5809447 A B P op f a t h1 h2)). Qed.
Lemma lem5809449 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : term112 A B a t P f) (h2 : term201 A B P op f a t) : term272 A B a P op t f.
Proof. exact (EQ_MP (@lem5809448 A B P op f a t h1 h2) (@lem0)). Qed.
Lemma lem5809450 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : term25 B P op) (h2 : term112 A B a t P f) (h3 : term201 A B P op f a t) : (term263 A B P a op t f) = True.
Proof. exact (@lem5809384 A B a t f P op h1 (@lem5809449 A B P op f a t h2 h3)). Qed.
Lemma lem5809451 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : term25 B P op) (h2 : @monoidal B op) (h3 : term112 A B a t P f) (h4 : term201 A B P op f a t) : (term115 A B P op a t f) = True.
Proof. exact (TRANS (@lem5809380 A B P op f a t h2 h4) (@lem5809450 A B P op f a t h1 h3 h4)). Qed.
Lemma lem5809452 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : term25 B P op) (h2 : @monoidal B op) (h3 : term201 A B P op f a t) : term273 A B P op a t f.
Proof. exact (fun h0 : term112 A B a t P f => @lem5809451 A B P op f a t h1 h2 h0 h3). Qed.
Lemma lem5809453 {A B : Type'} (op : type1400 B) (a : A) (t : A -> Prop) (P : B -> Prop) (f : A -> B) : term274 A B op a t P f.
Proof. exact (@lem5809299 A B op a t P f True). Qed.
Lemma lem5809454 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : term25 B P op) (h2 : @monoidal B op) (h3 : term201 A B P op f a t) : (term117 A B P op a t f) = (term275 A B a t P f).
Proof. exact (@lem5809453 A B op a t P f (@lem5809452 A B P op f a t h1 h2 h3)). Qed.
Lemma lem5809456 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5809457 {A B : Type'} (a : A) (t : A -> Prop) (P : B -> Prop) (f : A -> B) : (term275 A B a t P f) = True.
Proof. exact (@lem5809456 (term112 A B a t P f)). Qed.
Lemma lem5809458 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) (h1 : term25 B P op) (h2 : @monoidal B op) (h3 : term201 A B P op f a t) : (term117 A B P op a t f) = True.
Proof. exact (TRANS (@lem5809454 A B P op f a t h1 h2 h3) (@lem5809457 A B a t P f)). Qed.
Lemma lem5809459 {A B : Type'} (a : A) (t : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term25 B P op) (h2 : @monoidal B op) : term276 A B P op a t f.
Proof. exact (fun h0 : term201 A B P op f a t => @lem5809458 A B P op f a t h1 h2 h0). Qed.
Lemma lem5809460 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) : term277 A B P op f a t.
Proof. exact (@lem5809236 A B P op f a t True). Qed.
Lemma lem5809461 {A B : Type'} (f : A -> B) (a : A) (t : A -> Prop) (P : B -> Prop) (op : type1400 B) (h1 : term25 B P op) (h2 : @monoidal B op) : (term206 A B P op a t f) = (term278 A B P op f a t).
Proof. exact (@lem5809460 A B P op f a t (@lem5809459 A B a t f P op h1 h2)). Qed.
Lemma lem5809463 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5809464 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (a : A) (t : A -> Prop) : (term278 A B P op f a t) = True.
Proof. exact (@lem5809463 (term201 A B P op f a t)). Qed.
Lemma lem5809465 {A B : Type'} (a : A) (t : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term25 B P op) (h2 : @monoidal B op) : (term206 A B P op a t f) = True.
Proof. exact (TRANS (@lem5809461 A B f a t P op h1 h2) (@lem5809464 A B P op f a t)). Qed.
Lemma lem5809466 {A B : Type'} (a : A) (t : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term25 B P op) (h2 : @monoidal B op) : True = (term206 A B P op a t f).
Proof. exact (SYM (@lem5809465 A B a t f P op h1 h2)). Qed.
Lemma lem5809467 {A B : Type'} (a : A) (t : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term25 B P op) (h2 : @monoidal B op) : term206 A B P op a t f.
Proof. exact (EQ_MP (@lem5809466 A B a t f P op h1 h2) (@lem0)). Qed.
Lemma lem5809468 {A B : Type'} (a : A) (f : A -> B) (P : B -> Prop) (op : type1400 B) (t : A -> Prop) (h1 : term25 B P op) (h2 : @monoidal B op) (h3 : term2 A t) : term119 A B P op a t f.
Proof. exact (EQ_MP (@lem5809063 A B P op a f t h3) (@lem5809467 A B a t f P op h1 h2)). Qed.
Lemma lem5809469 {A B : Type'} (a : A) (t : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term25 B P op) (h2 : @monoidal B op) : term119 A B P op a t f.
Proof. exact (or_elim (@lem5807178 A t) (fun h0 : t = (@EMPTY A) => @lem5808079 A B P a f op t h2 h0) (fun h0 : term2 A t => @lem5809468 A B a f P op t h1 h2 h0)). Qed.
Lemma lem5809474 {A B : Type'} (a : A) (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term25 B P op) (h2 : @monoidal B op) : term121 A B P op a f.
Proof. exact (fun t : A -> Prop => @lem5809469 A B a t f P op h1 h2). Qed.
Lemma lem5809479 {A B : Type'} (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term25 B P op) (h2 : @monoidal B op) : term123 A B P op f.
Proof. exact (fun a : A => @lem5809474 A B a f P op h1 h2). Qed.
Lemma lem5809480 {A B : Type'} (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term25 B P op) (h2 : @monoidal B op) : term68 A B P op f.
Proof. exact (EQ_MP (@lem5807511 A B P op f) (@lem5809479 A B f P op h1 h2)). Qed.
Lemma lem5809481 {A B : Type'} (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term25 B P op) (h2 : @monoidal B op) : term40 A B P op f.
Proof. exact (@lem5807301 A B P op f (@lem5809480 A B f P op h1 h2)). Qed.
Lemma lem5809482 {A B : Type'} (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term25 B P op) (h2 : @monoidal B op) : term39 A B P op f.
Proof. exact (EQ_MP (@lem5807268 A B P op f) (@lem5809481 A B f P op h1 h2)). Qed.
Lemma lem5809487 {A B : Type'} (P : B -> Prop) (op : type1400 B) (h1 : term25 B P op) (h2 : @monoidal B op) : term279 A B P op.
Proof. exact (fun f : A -> B => @lem5809482 A B f P op h1 h2). Qed.
Lemma lem5809488 {A B : Type'} (P : B -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term280 A B P op.
Proof. exact (fun h0 : term25 B P op => @lem5809487 A B P op h0 h1). Qed.
Lemma lem5809493 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term281 A B op.
Proof. exact (fun P : B -> Prop => @lem5809488 A B P op h1). Qed.
Lemma lem5809494 {A B : Type'} (op : type1400 B) : term282 A B op.
Proof. exact (fun h0 : @monoidal B op => @lem5809493 A B op h0). Qed.
Lemma lem5809499 {A B : Type'} : term283 A B.
Proof. exact (fun op : type1400 B => @lem5809494 A B op). Qed.
