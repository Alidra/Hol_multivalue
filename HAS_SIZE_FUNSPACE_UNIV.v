Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SIZE_FUNSPACE_UNIV_term_abbrevs.
Require Import HAS_SIZE_FUNSPACE_spec.
Require Import IN_UNIV_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm3399787_spec.
Require Import thm3399835_spec.
Require Import thm7_spec.
Lemma lem4582116 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204818 A x). Qed.
Lemma lem4582117 {A : Type'} (x : A) : (term0 A x) = (@IN A x (@UNIV A)).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem4582118 {A : Type'} (x : A) : @IN A x (@UNIV A).
Proof. exact (EQ_MP (@lem4582117 A x) (@lem4582116 A x)). Qed.
Lemma lem4582119 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = ((@IN A x (@UNIV A)) = True).
Proof. exact (@lem7 (@IN A x (@UNIV A))). Qed.
Lemma lem4582121 {A B : Type'} (h1 : term1 A B) : term1 A B.
Proof. exact (h1). Qed.
Lemma lem4582122 {A B : Type'} (d : B) (h1 : term1 A B) : term2 A B d.
Proof. exact (@lem4582121 A B h1 d). Qed.
Lemma lem4582123 {A B : Type'} (d : B) : (term2 A B d) = (term3 A B d).
Proof. exact (eq_refl (term2 A B d)). Qed.
Lemma lem4582124 {A B : Type'} (d : B) (h1 : term1 A B) : term3 A B d.
Proof. exact (EQ_MP (@lem4582123 A B d) (@lem4582122 A B d h1)). Qed.
Lemma lem4582125 {A B : Type'} (d : B) (n : nat) (h1 : term1 A B) : term4 A B d n.
Proof. exact (@lem4582124 A B d h1 n). Qed.
Lemma lem4582126 {A B : Type'} (d : B) (n : nat) : (term4 A B d n) = (term5 A B d n).
Proof. exact (eq_refl (term4 A B d n)). Qed.
Lemma lem4582127 {A B : Type'} (d : B) (n : nat) (h1 : term1 A B) : term5 A B d n.
Proof. exact (EQ_MP (@lem4582126 A B d n) (@lem4582125 A B d n h1)). Qed.
Lemma lem4582128 {A B : Type'} (d : B) (n : nat) (t : B -> Prop) (h1 : term1 A B) : term6 A B d n t.
Proof. exact (@lem4582127 A B d n h1 t). Qed.
Lemma lem4582129 {A B : Type'} (t : B -> Prop) (d : B) (n : nat) : (term6 A B d n t) = (term7 A B t d n).
Proof. exact (eq_refl (term6 A B d n t)). Qed.
Lemma lem4582130 {A B : Type'} (t : B -> Prop) (d : B) (n : nat) (h1 : term1 A B) : term7 A B t d n.
Proof. exact (EQ_MP (@lem4582129 A B t d n) (@lem4582128 A B d n t h1)). Qed.
Lemma lem4582131 {A B : Type'} (t : B -> Prop) (d : B) (n : nat) (m : nat) (h1 : term1 A B) : term8 A B t d n m.
Proof. exact (@lem4582130 A B t d n h1 m). Qed.
Lemma lem4582132 {A B : Type'} (t : B -> Prop) (d : B) (n : nat) (m : nat) : (term8 A B t d n m) = (term9 A B t d n m).
Proof. exact (eq_refl (term8 A B t d n m)). Qed.
Lemma lem4582133 {A B : Type'} (t : B -> Prop) (d : B) (n : nat) (m : nat) (h1 : term1 A B) : term9 A B t d n m.
Proof. exact (EQ_MP (@lem4582132 A B t d n m) (@lem4582131 A B t d n m h1)). Qed.
Lemma lem4582134 {A B : Type'} (t : B -> Prop) (d : B) (n : nat) (m : nat) (s : A -> Prop) (h1 : term1 A B) : term10 A B t d n m s.
Proof. exact (@lem4582133 A B t d n m h1 s). Qed.
Lemma lem4582135 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (d : B) (n : nat) (m : nat) : (term10 A B t d n m s) = (term11 A B t s d n m).
Proof. exact (eq_refl (term10 A B t d n m s)). Qed.
Lemma lem4582136 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (d : B) (n : nat) (m : nat) (h1 : term1 A B) : term11 A B t s d n m.
Proof. exact (EQ_MP (@lem4582135 A B t s d n m) (@lem4582134 A B t d n m s h1)). Qed.
Lemma lem4582137 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term12 A B s m t n) : term12 A B s m t n.
Proof. exact (h1). Qed.
Lemma lem4582138 {A B : Type'} (d : B) (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term1 A B) (h2 : term12 A B s m t n) : term13 A B t s d n m.
Proof. exact (@lem4582136 A B t s d n m h1 (@lem4582137 A B s m t n h2)). Qed.
Lemma lem4582139 {A B : Type'} (s : A -> Prop) (m : nat) (t : B -> Prop) (n : nat) (h1 : term1 A B) (h2 : term12 A B s m t n) : term14 A B t s n m.
Proof. exact (fun d : B => @lem4582138 A B d s m t n h1 h2). Qed.
Lemma lem4582140 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (n : nat) (m : nat) (h1 : term1 A B) : term15 A B t s n m.
Proof. exact (fun h0 : term12 A B s m t n => @lem4582139 A B s m t n h1 h0). Qed.
Lemma lem4582141 {A B : Type'} (t : B -> Prop) (n : nat) (m : nat) (h1 : term1 A B) : term16 A B t n m.
Proof. exact (fun s : A -> Prop => @lem4582140 A B t s n m h1). Qed.
Lemma lem4582142 {A B : Type'} (t : B -> Prop) (n : nat) (h1 : term1 A B) : term17 A B t n.
Proof. exact (fun m : nat => @lem4582141 A B t n m h1). Qed.
Lemma lem4582143 {A B : Type'} (n : nat) (h1 : term1 A B) : term18 A B n.
Proof. exact (fun t : B -> Prop => @lem4582142 A B t n h1). Qed.
Lemma lem4582144 {A B : Type'} (h1 : term1 A B) : term19 A B.
Proof. exact (fun n : nat => @lem4582143 A B n h1). Qed.
Lemma lem4582145 {A B : Type'} : term20 A B.
Proof. exact (fun h0 : term1 A B => @lem4582144 A B h0). Qed.
Lemma lem4582146 {A B : Type'} : term19 A B.
Proof. exact (@lem4582145 A B (@lem4521678 A B)). Qed.
Lemma lem4582147 {A B : Type'} (n : nat) : term21 A B n.
Proof. exact (@lem4582146 A B n). Qed.
Lemma lem4582148 {A B : Type'} (n : nat) : (term21 A B n) = (term18 A B n).
Proof. exact (eq_refl (term21 A B n)). Qed.
Lemma lem4582149 {A B : Type'} (n : nat) : term18 A B n.
Proof. exact (EQ_MP (@lem4582148 A B n) (@lem4582147 A B n)). Qed.
Lemma lem4582150 {A B : Type'} (n : nat) (t : B -> Prop) : term22 A B n t.
Proof. exact (@lem4582149 A B n t). Qed.
Lemma lem4582151 {A B : Type'} (t : B -> Prop) (n : nat) : (term22 A B n t) = (term17 A B t n).
Proof. exact (eq_refl (term22 A B n t)). Qed.
Lemma lem4582152 {A B : Type'} (t : B -> Prop) (n : nat) : term17 A B t n.
Proof. exact (EQ_MP (@lem4582151 A B t n) (@lem4582150 A B n t)). Qed.
Lemma lem4582153 {A B : Type'} (t : B -> Prop) (n : nat) (m : nat) : term23 A B t n m.
Proof. exact (@lem4582152 A B t n m). Qed.
Lemma lem4582154 {A B : Type'} (t : B -> Prop) (n : nat) (m : nat) : (term23 A B t n m) = (term16 A B t n m).
Proof. exact (eq_refl (term23 A B t n m)). Qed.
Lemma lem4582155 {A B : Type'} (t : B -> Prop) (n : nat) (m : nat) : term16 A B t n m.
Proof. exact (EQ_MP (@lem4582154 A B t n m) (@lem4582153 A B t n m)). Qed.
Lemma lem4582156 {A B : Type'} (t : B -> Prop) (n : nat) (m : nat) (s : A -> Prop) : term24 A B t n m s.
Proof. exact (@lem4582155 A B t n m s). Qed.
Lemma lem4582157 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (n : nat) (m : nat) : (term24 A B t n m s) = (term15 A B t s n m).
Proof. exact (eq_refl (term24 A B t n m s)). Qed.
Lemma lem4582159 {A B : Type'} (m : nat) (n : nat) (h1 : term25 A B m n) : term25 A B m n.
Proof. exact (h1). Qed.
Lemma lem4582161 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (n : nat) (m : nat) : term15 A B t s n m.
Proof. exact (EQ_MP (@lem4582157 A B t s n m) (@lem4582156 A B t n m s)). Qed.
Lemma lem4582162 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (n : nat) (m : nat) : term15 A B t s n m.
Proof. exact (@lem4582161 A B t s n m). Qed.
Lemma lem4582163 {A B : Type'} (n : nat) (m : nat) : term26 A B n m.
Proof. exact (@lem4582162 A B (@UNIV B) (@UNIV A) n m). Qed.
Lemma lem4582164 {A B : Type'} (m : nat) (n : nat) (h1 : term25 A B m n) : term27 A B n m.
Proof. exact (@lem4582163 A B n m (@lem4582159 A B m n h1)). Qed.
Lemma lem4582184 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem4582119 A x) (@lem4582118 A x)). Qed.
Lemma lem4582185 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem4582184 A x). Qed.
Lemma lem4582186 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4582187 {A : Type'} (x : A) : (term28 A x) = (imp True).
Proof. exact (MK_COMB (@lem4582186) (@lem4582185 A x)). Qed.
Lemma lem4582189 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem4582119 A x) (@lem4582118 A x)). Qed.
Lemma lem4582190 {B : Type'} (x : B) : (@IN B x (@UNIV B)) = True.
Proof. exact (@lem4582189 B x). Qed.
Lemma lem4582191 {A B : Type'} (f : A -> B) (x : A) : (term29 A B f x) = True.
Proof. exact (@lem4582190 B (f x)). Qed.
Lemma lem4582192 {A B : Type'} (f : A -> B) (x : A) : (term30 A B f x) = (True -> True).
Proof. exact (MK_COMB (@lem4582187 A x) (@lem4582191 A B f x)). Qed.
Lemma lem4582194 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4582195 : (True -> True) = True.
Proof. exact (@lem4582194 True). Qed.
Lemma lem4582196 {A B : Type'} (f : A -> B) (x : A) : (term30 A B f x) = True.
Proof. exact (TRANS (@lem4582192 A B f x) (@lem4582195)). Qed.
Lemma lem4582197 {A B : Type'} (f : A -> B) : (term31 A B f) = (term32 A).
Proof. exact (fun_ext (fun x : A => @lem4582196 A B f x)). Qed.
Lemma lem4582198 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4582199 {A B : Type'} (f : A -> B) : (term33 A B f) = (term34 A).
Proof. exact (MK_COMB (@lem4582198 A) (@lem4582197 A B f)). Qed.
Lemma lem4582201 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4582202 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (@lem4582201 A t). Qed.
Lemma lem4582203 {A : Type'} : (term34 A) = True.
Proof. exact (@lem4582202 A True). Qed.
Lemma lem4582204 {A B : Type'} (f : A -> B) : (term33 A B f) = True.
Proof. exact (TRANS (@lem4582199 A B f) (@lem4582203 A)). Qed.
Lemma lem4582205 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4582206 {A B : Type'} (f : A -> B) : (term36 A B f) = (and True).
Proof. exact (MK_COMB (@lem4582205) (@lem4582204 A B f)). Qed.
Lemma lem4582214 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem4582119 A x) (@lem4582118 A x)). Qed.
Lemma lem4582215 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem4582214 A x). Qed.
Lemma lem4582216 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4582217 {A : Type'} (x : A) : (term37 A x) = (~ True).
Proof. exact (MK_COMB (@lem4582216) (@lem4582215 A x)). Qed.
Lemma lem4582219 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem4582220 {A : Type'} (x : A) : (term37 A x) = False.
Proof. exact (TRANS (@lem4582217 A x) (@lem4582219)). Qed.
Lemma lem4582221 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4582222 {A : Type'} (x : A) : (term38 A x) = (imp False).
Proof. exact (MK_COMB (@lem4582221) (@lem4582220 A x)). Qed.
Lemma lem4582225 {A B : Type'} (f : A -> B) (x : A) (d : B) : ((f x) = d) = ((f x) = d).
Proof. exact (eq_refl ((f x) = d)). Qed.
Lemma lem4582226 {A B : Type'} (f : A -> B) (x : A) (d : B) : (term39 A B f x d) = (term40 A B f x d).
Proof. exact (MK_COMB (@lem4582222 A x) (@lem4582225 A B f x d)). Qed.
Lemma lem4582228 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4582229 {A B : Type'} (f : A -> B) (x : A) (d : B) : (term40 A B f x d) = True.
Proof. exact (@lem4582228 ((f x) = d)). Qed.
Lemma lem4582230 {A B : Type'} (f : A -> B) (x : A) (d : B) : (term39 A B f x d) = True.
Proof. exact (TRANS (@lem4582226 A B f x d) (@lem4582229 A B f x d)). Qed.
Lemma lem4582231 {A B : Type'} (f : A -> B) (d : B) : (term41 A B f d) = (term32 A).
Proof. exact (fun_ext (fun x : A => @lem4582230 A B f x d)). Qed.
Lemma lem4582232 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4582233 {A B : Type'} (f : A -> B) (d : B) : (term42 A B f d) = (term34 A).
Proof. exact (MK_COMB (@lem4582232 A) (@lem4582231 A B f d)). Qed.
Lemma lem4582235 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4582236 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (@lem4582235 A t). Qed.
Lemma lem4582237 {A : Type'} : (term34 A) = True.
Proof. exact (@lem4582236 A True). Qed.
Lemma lem4582238 {A B : Type'} (f : A -> B) (d : B) : (term42 A B f d) = True.
Proof. exact (TRANS (@lem4582233 A B f d) (@lem4582237 A)). Qed.
Lemma lem4582239 {A B : Type'} (f : A -> B) (d : B) : (term43 A B f d) = (True /\ True).
Proof. exact (MK_COMB (@lem4582206 A B f) (@lem4582238 A B f d)). Qed.
Lemma lem4582241 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4582242 : (True /\ True) = True.
Proof. exact (@lem4582241 True). Qed.
Lemma lem4582243 {A B : Type'} (f : A -> B) (d : B) : (term43 A B f d) = True.
Proof. exact (TRANS (@lem4582239 A B f d) (@lem4582242)). Qed.
Lemma lem4582244 {A B : Type'} (GEN_PVAR_148 : A -> B) : (@SETSPEC (A -> B) GEN_PVAR_148) = (@SETSPEC (A -> B) GEN_PVAR_148).
Proof. exact (eq_refl (@SETSPEC (A -> B) GEN_PVAR_148)). Qed.
Lemma lem4582245 {A B : Type'} (f : A -> B) (d : B) (GEN_PVAR_148 : A -> B) : (term44 A B GEN_PVAR_148 f d) = (@SETSPEC (A -> B) GEN_PVAR_148 True).
Proof. exact (MK_COMB (@lem4582244 A B GEN_PVAR_148) (@lem4582243 A B f d)). Qed.
Lemma lem4582246 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4582247 {A B : Type'} (d : B) (GEN_PVAR_148 : A -> B) (f : A -> B) : (term45 A B GEN_PVAR_148 d f) = (@SETSPEC (A -> B) GEN_PVAR_148 True f).
Proof. exact (MK_COMB (@lem4582245 A B f d GEN_PVAR_148) (@lem4582246 A B f)). Qed.
Lemma lem4582248 {A B : Type'} (d : B) (GEN_PVAR_148 : A -> B) : (term46 A B GEN_PVAR_148 d) = (term47 A B GEN_PVAR_148).
Proof. exact (fun_ext (fun f : A -> B => @lem4582247 A B d GEN_PVAR_148 f)). Qed.
Lemma lem4582249 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem4582250 {A B : Type'} (d : B) (GEN_PVAR_148 : A -> B) : (term48 A B GEN_PVAR_148 d) = (term49 A B GEN_PVAR_148).
Proof. exact (MK_COMB (@lem4582249 A B) (@lem4582248 A B d GEN_PVAR_148)). Qed.
Lemma lem4582255 {A B : Type'} (d : B) : (term50 A B d) = (term51 A B).
Proof. exact (fun_ext (fun GEN_PVAR_148 : A -> B => @lem4582250 A B d GEN_PVAR_148)). Qed.
Lemma lem4582256 {A B : Type'} : (@GSPEC (A -> B)) = (@GSPEC (A -> B)).
Proof. exact (eq_refl (@GSPEC (A -> B))). Qed.
Lemma lem4582257 {A B : Type'} (d : B) : (term52 A B d) = (term53 A B).
Proof. exact (MK_COMB (@lem4582256 A B) (@lem4582255 A B d)). Qed.
Lemma lem4582259 {_88312 : Type'} : (term54 _88312) = (@UNIV _88312).
Proof. exact (EQ_MP (@lem3399787 _88312) (@lem3399835 _88312)). Qed.
Lemma lem4582260 {A B : Type'} : (term53 A B) = (@UNIV (A -> B)).
Proof. exact (@lem4582259 (A -> B)). Qed.
Lemma lem4582261 {A B : Type'} (d : B) : (term52 A B d) = (@UNIV (A -> B)).
Proof. exact (TRANS (@lem4582257 A B d) (@lem4582260 A B)). Qed.
Lemma lem4582262 {A B : Type'} : (@HAS_SIZE (A -> B)) = (@HAS_SIZE (A -> B)).
Proof. exact (eq_refl (@HAS_SIZE (A -> B))). Qed.
Lemma lem4582263 {A B : Type'} (d : B) : (term55 A B d) = (@HAS_SIZE (A -> B) (@UNIV (A -> B))).
Proof. exact (MK_COMB (@lem4582262 A B) (@lem4582261 A B d)). Qed.
Lemma lem4582264 (n : nat) (m : nat) : (Nat.pow n m) = (Nat.pow n m).
Proof. exact (eq_refl (Nat.pow n m)). Qed.
Lemma lem4582265 {A B : Type'} (d : B) (n : nat) (m : nat) : (term56 A B d n m) = (term57 A B n m).
Proof. exact (MK_COMB (@lem4582263 A B d) (@lem4582264 n m)). Qed.
Lemma lem4582266 {A B : Type'} (n : nat) (m : nat) : (term58 A B n m) = (term59 A B n m).
Proof. exact (fun_ext (fun d : B => @lem4582265 A B d n m)). Qed.
Lemma lem4582267 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4582268 {A B : Type'} (n : nat) (m : nat) : (term27 A B n m) = (term60 A B n m).
Proof. exact (MK_COMB (@lem4582267 B) (@lem4582266 A B n m)). Qed.
Lemma lem4582270 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4582271 {B : Type'} (t : Prop) : (term35 B t) = t.
Proof. exact (@lem4582270 B t). Qed.
Lemma lem4582272 {A B : Type'} (n : nat) (m : nat) : (term60 A B n m) = (term57 A B n m).
Proof. exact (@lem4582271 B (term57 A B n m)). Qed.
Lemma lem4582273 {A B : Type'} (n : nat) (m : nat) : (term27 A B n m) = (term57 A B n m).
Proof. exact (TRANS (@lem4582268 A B n m) (@lem4582272 A B n m)). Qed.
Lemma lem4582274 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4582275 {A B : Type'} (n : nat) (m : nat) : (term61 A B n m) = (term62 A B n m).
Proof. exact (MK_COMB (@lem4582274) (@lem4582273 A B n m)). Qed.
Lemma lem4582276 {A B : Type'} (n : nat) (m : nat) : (term57 A B n m) = (term57 A B n m).
Proof. exact (eq_refl (term57 A B n m)). Qed.
Lemma lem4582277 {A B : Type'} (n : nat) (m : nat) : (term63 A B n m) = (term64 A B n m).
Proof. exact (MK_COMB (@lem4582275 A B n m) (@lem4582276 A B n m)). Qed.
Lemma lem4582279 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem4582280 {A B : Type'} (n : nat) (m : nat) : (term64 A B n m) = True.
Proof. exact (@lem4582279 (term57 A B n m)). Qed.
Lemma lem4582281 {A B : Type'} (n : nat) (m : nat) : (term63 A B n m) = True.
Proof. exact (TRANS (@lem4582277 A B n m) (@lem4582280 A B n m)). Qed.
Lemma lem4582282 {A B : Type'} (n : nat) (m : nat) : True = (term63 A B n m).
Proof. exact (SYM (@lem4582281 A B n m)). Qed.
Lemma lem4582283 {A B : Type'} (n : nat) (m : nat) : term63 A B n m.
Proof. exact (EQ_MP (@lem4582282 A B n m) (@lem0)). Qed.
Lemma lem4582284 {A B : Type'} (m : nat) (n : nat) (h1 : term25 A B m n) : term57 A B n m.
Proof. exact (@lem4582283 A B n m (@lem4582164 A B m n h1)). Qed.
Lemma lem4582285 {A B : Type'} (n : nat) (m : nat) : term65 A B n m.
Proof. exact (fun h0 : term25 A B m n => @lem4582284 A B m n h0). Qed.
Lemma lem4582290 {A B : Type'} (m : nat) : term66 A B m.
Proof. exact (fun n : nat => @lem4582285 A B n m). Qed.
Lemma lem4582295 {A B : Type'} : term67 A B.
Proof. exact (fun m : nat => @lem4582290 A B m). Qed.
