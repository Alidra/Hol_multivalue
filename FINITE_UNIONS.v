Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_UNIONS_term_abbrevs.
Require Import CONTRAPOS_THM_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import FINITE_FINITE_UNIONS_spec.
Require Import FINITE_POWERSET_spec.
Require Import FINITE_SUBSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm1823_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211662_spec.
Require Import thm3211663_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm951_spec.
Require Import thm952_spec.
Lemma lem4605039 (q : Prop) (p : Prop) (r : Prop) : (term0 p q r) = (term1 q p r).
Proof. exact (EQ_MP (@lem952 q p r) (@lem951 p q r)). Qed.
Lemma lem4605040 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term2 A t s) = (term3 A t s).
Proof. exact (@lem4605039 (@SUBSET A s t) (@FINITE A t) (@FINITE A s)). Qed.
Lemma lem4605045 {A : Type'} (s : A -> Prop) : (term4 A s) = (term5 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4605040 A t s)). Qed.
Lemma lem4605046 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4605047 {A : Type'} (s : A -> Prop) : (term6 A s) = (term7 A s).
Proof. exact (MK_COMB (@lem4605046 A) (@lem4605045 A s)). Qed.
Lemma lem4605052 {A : Type'} : (term8 A) = (term9 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4605047 A s)). Qed.
Lemma lem4605053 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4605054 {A : Type'} : (term10 A) = (term11 A).
Proof. exact (MK_COMB (@lem4605053 A) (@lem4605052 A)). Qed.
Lemma lem4605059 {A : Type'} : term11 A.
Proof. exact (EQ_MP (@lem4605054 A) (@lem3599924 A)). Qed.
Lemma lem4605060 {A : Type'} (h1 : term11 A) : term11 A.
Proof. exact (h1). Qed.
Lemma lem4605061 {A : Type'} (s : A -> Prop) (h1 : term11 A) : term12 A s.
Proof. exact (@lem4605060 A h1 s). Qed.
Lemma lem4605062 {A : Type'} (s : A -> Prop) : (term12 A s) = (term7 A s).
Proof. exact (eq_refl (term12 A s)). Qed.
Lemma lem4605063 {A : Type'} (s : A -> Prop) (h1 : term11 A) : term7 A s.
Proof. exact (EQ_MP (@lem4605062 A s) (@lem4605061 A s h1)). Qed.
Lemma lem4605064 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term11 A) : term13 A s t.
Proof. exact (@lem4605063 A s h1 t). Qed.
Lemma lem4605065 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term13 A s t) = (term3 A t s).
Proof. exact (eq_refl (term13 A s t)). Qed.
Lemma lem4605066 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term11 A) : term3 A t s.
Proof. exact (EQ_MP (@lem4605065 A t s) (@lem4605064 A s t h1)). Qed.
Lemma lem4605067 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @SUBSET A s t) : @SUBSET A s t.
Proof. exact (h1). Qed.
Lemma lem4605068 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term11 A) (h2 : @SUBSET A s t) : term14 A t s.
Proof. exact (@lem4605066 A t s h1 (@lem4605067 A s t h2)). Qed.
Lemma lem4605069 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @SUBSET A s t) : term15 A t s.
Proof. exact (fun h0 : term11 A => @lem4605068 A s t h0 h1). Qed.
Lemma lem4605070 {A : Type'} (h1 : term11 A) : term11 A.
Proof. exact (h1). Qed.
Lemma lem4605071 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term11 A) (h2 : @SUBSET A s t) : term14 A t s.
Proof. exact (@lem4605069 A s t h2 (@lem4605070 A h1)). Qed.
Lemma lem4605072 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term11 A) : term3 A t s.
Proof. exact (fun h0 : @SUBSET A s t => @lem4605071 A s t h1 h0). Qed.
Lemma lem4605073 {A : Type'} (t : A -> Prop) (h1 : term11 A) : term16 A t.
Proof. exact (fun s : A -> Prop => @lem4605072 A t s h1). Qed.
Lemma lem4605074 {A : Type'} (h1 : term11 A) : term17 A.
Proof. exact (fun t : A -> Prop => @lem4605073 A t h1). Qed.
Lemma lem4605075 {A : Type'} : term18 A.
Proof. exact (fun h0 : term11 A => @lem4605074 A h0). Qed.
Lemma lem4605076 {A : Type'} : term17 A.
Proof. exact (@lem4605075 A (@lem4605059 A)). Qed.
Lemma lem4605077 {A : Type'} (t : A -> Prop) : term19 A t.
Proof. exact (@lem4605076 A t). Qed.
Lemma lem4605078 {A : Type'} (t : A -> Prop) : (term19 A t) = (term16 A t).
Proof. exact (eq_refl (term19 A t)). Qed.
Lemma lem4605079 {A : Type'} (t : A -> Prop) : term16 A t.
Proof. exact (EQ_MP (@lem4605078 A t) (@lem4605077 A t)). Qed.
Lemma lem4605080 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term20 A t s.
Proof. exact (@lem4605079 A t s). Qed.
Lemma lem4605081 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term20 A t s) = (term3 A t s).
Proof. exact (eq_refl (term20 A t s)). Qed.
Lemma lem4605083 (t1 : Prop) : term21 t1.
Proof. exact (@lem10414 t1). Qed.
Lemma lem4605084 (t1 : Prop) : (term21 t1) = (term22 t1).
Proof. exact (eq_refl (term21 t1)). Qed.
Lemma lem4605085 (t1 : Prop) : term22 t1.
Proof. exact (EQ_MP (@lem4605084 t1) (@lem4605083 t1)). Qed.
Lemma lem4605086 (t1 : Prop) (t2 : Prop) : term23 t1 t2.
Proof. exact (@lem4605085 t1 t2). Qed.
Lemma lem4605087 (t2 : Prop) (t1 : Prop) : (term23 t1 t2) = ((term24 t1 t2) = (t2 -> t1)).
Proof. exact (eq_refl (term23 t1 t2)). Qed.
Lemma lem4605089 {A : Type'} (s : A -> Prop) : term25 A s.
Proof. exact (@lem4603107 A s). Qed.
Lemma lem4605090 {A : Type'} (s : A -> Prop) : (term25 A s) = (term26 A s).
Proof. exact (eq_refl (term25 A s)). Qed.
Lemma lem4605092 {A : Type'} (s : type686 A) : term27 A s.
Proof. exact (@lem9784 (@FINITE (A -> Prop) s)). Qed.
Lemma lem4605093 {A : Type'} (s : type686 A) : (term27 A s) = (term28 A s).
Proof. exact (eq_refl (term27 A s)). Qed.
Lemma lem4605094 {A : Type'} (s : type686 A) : term28 A s.
Proof. exact (EQ_MP (@lem4605093 A s) (@lem4605092 A s)). Qed.
Lemma lem4605095 {A : Type'} (s : type686 A) (h1 : @FINITE (A -> Prop) s) : @FINITE (A -> Prop) s.
Proof. exact (h1). Qed.
Lemma lem4605096 {A : Type'} (s : type686 A) (h1 : term29 A s) : term29 A s.
Proof. exact (h1). Qed.
Lemma lem4605097 {_92445 : Type'} (s : type686 _92445) : term30 _92445 s.
Proof. exact (@lem3612894 _92445 s). Qed.
Lemma lem4605098 {_92445 : Type'} (s : type686 _92445) : (term30 _92445 s) = (term31 _92445 s).
Proof. exact (eq_refl (term30 _92445 s)). Qed.
Lemma lem4605099 {_92445 : Type'} (s : type686 _92445) : term31 _92445 s.
Proof. exact (EQ_MP (@lem4605098 _92445 s) (@lem4605097 _92445 s)). Qed.
Lemma lem4605100 {_92445 : Type'} (s : type686 _92445) (h1 : @FINITE (_92445 -> Prop) s) : @FINITE (_92445 -> Prop) s.
Proof. exact (h1). Qed.
Lemma lem4605101 {_92445 : Type'} (s : type686 _92445) (h1 : @FINITE (_92445 -> Prop) s) : (term32 _92445 s) = (term33 _92445 s).
Proof. exact (@lem4605099 _92445 s (@lem4605100 _92445 s h1)). Qed.
Lemma lem4605107 {A : Type'} (s : type686 A) : (@FINITE (A -> Prop) s) = ((@FINITE (A -> Prop) s) = True).
Proof. exact (@lem7 (@FINITE (A -> Prop) s)). Qed.
Lemma lem4605112 {_92445 : Type'} (s : type686 _92445) : term31 _92445 s.
Proof. exact (fun h0 : @FINITE (_92445 -> Prop) s => @lem4605101 _92445 s h0). Qed.
Lemma lem4605113 {A : Type'} (s : type686 A) : term31 A s.
Proof. exact (@lem4605112 A s). Qed.
Lemma lem4605115 {A : Type'} (s : type686 A) (h1 : @FINITE (A -> Prop) s) : (@FINITE (A -> Prop) s) = True.
Proof. exact (EQ_MP (@lem4605107 A s) (@lem4605095 A s h1)). Qed.
Lemma lem4605116 {A : Type'} (s : type686 A) (h1 : @FINITE (A -> Prop) s) : True = (@FINITE (A -> Prop) s).
Proof. exact (SYM (@lem4605115 A s h1)). Qed.
Lemma lem4605117 {A : Type'} (s : type686 A) (h1 : @FINITE (A -> Prop) s) : @FINITE (A -> Prop) s.
Proof. exact (EQ_MP (@lem4605116 A s h1) (@lem0)). Qed.
Lemma lem4605118 {A : Type'} (s : type686 A) (h1 : @FINITE (A -> Prop) s) : (term32 A s) = (term33 A s).
Proof. exact (@lem4605113 A s (@lem4605117 A s h1)). Qed.
Lemma lem4605146 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4605147 {A : Type'} (s : type686 A) (h1 : @FINITE (A -> Prop) s) : (term34 A s) = (term35 A s).
Proof. exact (MK_COMB (@lem4605146) (@lem4605118 A s h1)). Qed.
Lemma lem4605178 {A : Type'} (s : type686 A) (h1 : @FINITE (A -> Prop) s) : (@FINITE (A -> Prop) s) = True.
Proof. exact (EQ_MP (@lem4605107 A s) (@lem4605095 A s h1)). Qed.
Lemma lem4605179 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4605180 {A : Type'} (s : type686 A) (h1 : @FINITE (A -> Prop) s) : (term36 A s) = (and True).
Proof. exact (MK_COMB (@lem4605179) (@lem4605178 A s h1)). Qed.
Lemma lem4605208 {A : Type'} (s : type686 A) : (term33 A s) = (term33 A s).
Proof. exact (eq_refl (term33 A s)). Qed.
Lemma lem4605209 {A : Type'} (s : type686 A) (h1 : @FINITE (A -> Prop) s) : (term37 A s) = (term38 A s).
Proof. exact (MK_COMB (@lem4605180 A s h1) (@lem4605208 A s)). Qed.
Lemma lem4605211 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4605212 {A : Type'} (s : type686 A) : (term38 A s) = (term33 A s).
Proof. exact (@lem4605211 (term33 A s)). Qed.
Lemma lem4605240 {A : Type'} (s : type686 A) (h1 : @FINITE (A -> Prop) s) : (term37 A s) = (term33 A s).
Proof. exact (TRANS (@lem4605209 A s h1) (@lem4605212 A s)). Qed.
Lemma lem4605241 {A : Type'} (s : type686 A) (h1 : @FINITE (A -> Prop) s) : ((term32 A s) = (term37 A s)) = ((term33 A s) = (term33 A s)).
Proof. exact (MK_COMB (@lem4605147 A s h1) (@lem4605240 A s h1)). Qed.
Lemma lem4605243 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4605244 (x : Prop) : (x = x) = True.
Proof. exact (@lem4605243 Prop x). Qed.
Lemma lem4605245 {A : Type'} (s : type686 A) : ((term33 A s) = (term33 A s)) = True.
Proof. exact (@lem4605244 (term33 A s)). Qed.
Lemma lem4605246 {A : Type'} (s : type686 A) (h1 : @FINITE (A -> Prop) s) : ((term32 A s) = (term37 A s)) = True.
Proof. exact (TRANS (@lem4605241 A s h1) (@lem4605245 A s)). Qed.
Lemma lem4605247 {A : Type'} (s : type686 A) (h1 : @FINITE (A -> Prop) s) : True = ((term32 A s) = (term37 A s)).
Proof. exact (SYM (@lem4605246 A s h1)). Qed.
Lemma lem4605248 {A : Type'} (s : type686 A) (h1 : @FINITE (A -> Prop) s) : (term32 A s) = (term37 A s).
Proof. exact (EQ_MP (@lem4605247 A s h1) (@lem0)). Qed.
Lemma lem4605259 {A : Type'} (s : type686 A) : term39 A s.
Proof. exact (@lem82 (@FINITE (A -> Prop) s)). Qed.
Lemma lem4605272 {A : Type'} (s : type686 A) (h1 : term29 A s) : (@FINITE (A -> Prop) s) = False.
Proof. exact (@lem4605259 A s (@lem4605096 A s h1)). Qed.
Lemma lem4605273 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4605274 {A : Type'} (s : type686 A) (h1 : term29 A s) : (term36 A s) = (and False).
Proof. exact (MK_COMB (@lem4605273) (@lem4605272 A s h1)). Qed.
Lemma lem4605302 {A : Type'} (s : type686 A) : (term33 A s) = (term33 A s).
Proof. exact (eq_refl (term33 A s)). Qed.
Lemma lem4605303 {A : Type'} (s : type686 A) (h1 : term29 A s) : (term37 A s) = (term40 A s).
Proof. exact (MK_COMB (@lem4605274 A s h1) (@lem4605302 A s)). Qed.
Lemma lem4605305 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4605306 {A : Type'} (s : type686 A) : (term40 A s) = False.
Proof. exact (@lem4605305 (term33 A s)). Qed.
Lemma lem4605307 {A : Type'} (s : type686 A) (h1 : term29 A s) : (term37 A s) = False.
Proof. exact (TRANS (@lem4605303 A s h1) (@lem4605306 A s)). Qed.
Lemma lem4605308 {A : Type'} (s : type686 A) : (term34 A s) = (term34 A s).
Proof. exact (eq_refl (term34 A s)). Qed.
Lemma lem4605309 {A : Type'} (s : type686 A) (h1 : term29 A s) : ((term32 A s) = (term37 A s)) = ((term32 A s) = False).
Proof. exact (MK_COMB (@lem4605308 A s) (@lem4605307 A s h1)). Qed.
Lemma lem4605311 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4605312 {A : Type'} (s : type686 A) : ((term32 A s) = False) = (term41 A s).
Proof. exact (@lem4605311 (term32 A s)). Qed.
Lemma lem4605319 {A : Type'} (s : type686 A) (h1 : term29 A s) : ((term32 A s) = (term37 A s)) = (term41 A s).
Proof. exact (TRANS (@lem4605309 A s h1) (@lem4605312 A s)). Qed.
Lemma lem4605320 {A : Type'} (s : type686 A) (h1 : term29 A s) : (term41 A s) = ((term32 A s) = (term37 A s)).
Proof. exact (SYM (@lem4605319 A s h1)). Qed.
Lemma lem4605321 {A : Type'} (s : type686 A) (h1 : term32 A s) : term32 A s.
Proof. exact (h1). Qed.
Lemma lem4605323 {A : Type'} (s : A -> Prop) : term26 A s.
Proof. exact (EQ_MP (@lem4605090 A s) (@lem4605089 A s)). Qed.
Lemma lem4605324 {A : Type'} (s : A -> Prop) : term26 A s.
Proof. exact (@lem4605323 A s). Qed.
Lemma lem4605325 {A : Type'} (s : type686 A) : term42 A s.
Proof. exact (@lem4605324 A (@UNIONS A s)). Qed.
Lemma lem4605326 {A : Type'} (s : type686 A) (h1 : term32 A s) : term43 A s.
Proof. exact (@lem4605325 A s (@lem4605321 A s h1)). Qed.
Lemma lem4605330 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem4605331 {A : Type'} (s : type686 A) : (term44 A s) = (term45 A s).
Proof. exact (@lem4605330 (term43 A s)). Qed.
Lemma lem4605336 {A : Type'} (s : type686 A) : (term46 A s) = (term46 A s).
Proof. exact (eq_refl (term46 A s)). Qed.
Lemma lem4605337 {A : Type'} (s : type686 A) : (term47 A s) = (term48 A s).
Proof. exact (MK_COMB (@lem4605336 A s) (@lem4605331 A s)). Qed.
Lemma lem4605339 (t2 : Prop) (t1 : Prop) : (term24 t1 t2) = (t2 -> t1).
Proof. exact (EQ_MP (@lem4605087 t2 t1) (@lem4605086 t1 t2)). Qed.
Lemma lem4605340 {A : Type'} (s : type686 A) : (term48 A s) = (term49 A s).
Proof. exact (@lem4605339 (term43 A s) (@FINITE (A -> Prop) s)). Qed.
Lemma lem4605347 {A : Type'} (s : type686 A) : (term47 A s) = (term49 A s).
Proof. exact (TRANS (@lem4605337 A s) (@lem4605340 A s)). Qed.
Lemma lem4605348 {A : Type'} (s : type686 A) : (term49 A s) = (term47 A s).
Proof. exact (SYM (@lem4605347 A s)). Qed.
Lemma lem4605350 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term3 A t s.
Proof. exact (EQ_MP (@lem4605081 A t s) (@lem4605080 A t s)). Qed.
Lemma lem4605351 {A : Type'} (t : type686 A) (s : type686 A) : term50 A t s.
Proof. exact (@lem4605350 (A -> Prop) t s). Qed.
Lemma lem4605352 {A : Type'} (s : type686 A) : term51 A s.
Proof. exact (@lem4605351 A (term52 A s) s). Qed.
Lemma lem4605354 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term53 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4605355 {A : Type'} (s : type686 A) (t : type686 A) : (@SUBSET (A -> Prop) s t) = (term54 A s t).
Proof. exact (@lem4605354 (A -> Prop) s t). Qed.
Lemma lem4605356 {A : Type'} (s : type686 A) : (term55 A s) = (term56 A s).
Proof. exact (@lem4605355 A s (term52 A s)). Qed.
Lemma lem4605368 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term53 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4605369 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term53 A s t).
Proof. exact (@lem4605368 A s t). Qed.
Lemma lem4605370 {A : Type'} (t : A -> Prop) (s : type686 A) : (term57 A t s) = (term58 A t s).
Proof. exact (@lem4605369 A t (@UNIONS A s)). Qed.
Lemma lem4605377 {A : Type'} (GEN_PVAR_155 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_155) = (@SETSPEC (A -> Prop) GEN_PVAR_155).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_155)). Qed.
Lemma lem4605378 {A : Type'} (GEN_PVAR_155 : A -> Prop) (t : A -> Prop) (s : type686 A) : (term59 A GEN_PVAR_155 t s) = (term60 A GEN_PVAR_155 t s).
Proof. exact (MK_COMB (@lem4605377 A GEN_PVAR_155) (@lem4605370 A t s)). Qed.
Lemma lem4605379 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4605380 {A : Type'} (GEN_PVAR_155 : A -> Prop) (s : type686 A) (t : A -> Prop) : (term61 A GEN_PVAR_155 s t) = (term62 A GEN_PVAR_155 s t).
Proof. exact (MK_COMB (@lem4605378 A GEN_PVAR_155 t s) (@lem4605379 A t)). Qed.
Lemma lem4605381 {A : Type'} (GEN_PVAR_155 : A -> Prop) (s : type686 A) : (term63 A GEN_PVAR_155 s) = (term64 A GEN_PVAR_155 s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4605380 A GEN_PVAR_155 s t)). Qed.
Lemma lem4605382 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4605383 {A : Type'} (GEN_PVAR_155 : A -> Prop) (s : type686 A) : (term65 A GEN_PVAR_155 s) = (term66 A GEN_PVAR_155 s).
Proof. exact (MK_COMB (@lem4605382 A) (@lem4605381 A GEN_PVAR_155 s)). Qed.
Lemma lem4605388 {A : Type'} (s : type686 A) : (term67 A s) = (term68 A s).
Proof. exact (fun_ext (fun GEN_PVAR_155 : A -> Prop => @lem4605383 A GEN_PVAR_155 s)). Qed.
Lemma lem4605389 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4605390 {A : Type'} (s : type686 A) : (term52 A s) = (term69 A s).
Proof. exact (MK_COMB (@lem4605389 A) (@lem4605388 A s)). Qed.
Lemma lem4605391 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x) = (@IN (A -> Prop) x).
Proof. exact (eq_refl (@IN (A -> Prop) x)). Qed.
Lemma lem4605392 {A : Type'} (x : A -> Prop) (s : type686 A) : (term70 A x s) = (term71 A x s).
Proof. exact (MK_COMB (@lem4605391 A x) (@lem4605390 A s)). Qed.
Lemma lem4605393 {A : Type'} (x : A -> Prop) (s : type686 A) : (term72 A x s) = (term72 A x s).
Proof. exact (eq_refl (term72 A x s)). Qed.
Lemma lem4605394 {A : Type'} (x : A -> Prop) (s : type686 A) : (term73 A x s) = (term74 A x s).
Proof. exact (MK_COMB (@lem4605393 A x s) (@lem4605392 A x s)). Qed.
Lemma lem4605397 {A : Type'} (s : type686 A) : (term75 A s) = (term76 A s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4605394 A x s)). Qed.
Lemma lem4605398 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4605399 {A : Type'} (s : type686 A) : (term56 A s) = (term77 A s).
Proof. exact (MK_COMB (@lem4605398 A) (@lem4605397 A s)). Qed.
Lemma lem4605404 {A : Type'} (s : type686 A) : (term55 A s) = (term77 A s).
Proof. exact (TRANS (@lem4605356 A s) (@lem4605399 A s)). Qed.
Lemma lem4605405 {A : Type'} (s : type686 A) : (term77 A s) = (term55 A s).
Proof. exact (SYM (@lem4605404 A s)). Qed.
Lemma lem4605413 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4605414 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4605413 (A -> Prop) P x). Qed.
Lemma lem4605415 {A : Type'} (s : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x s) = (s x).
Proof. exact (@lem4605414 A s x). Qed.
Lemma lem4605416 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4605417 {A : Type'} (s : type686 A) (x : A -> Prop) : (term72 A x s) = (term78 A s x).
Proof. exact (MK_COMB (@lem4605416) (@lem4605415 A s x)). Qed.
Lemma lem4605419 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term79 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem4605420 {A : Type'} (p : type686 A) (x : A -> Prop) : (term80 A x p) = (p x).
Proof. exact (@lem4605419 (A -> Prop) p x). Qed.
Lemma lem4605421 {A : Type'} (s : type686 A) (x : A -> Prop) : (term81 A x s) = (term82 A s x).
Proof. exact (@lem4605420 A (term83 A s) x). Qed.
Lemma lem4605422 {A : Type'} (t : A -> Prop) (s : type686 A) : (term82 A s t) = (term58 A t s).
Proof. exact (eq_refl (term82 A s t)). Qed.
Lemma lem4605423 {A : Type'} (GEN_PVAR_155 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_155) = (@SETSPEC (A -> Prop) GEN_PVAR_155).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_155)). Qed.
Lemma lem4605424 {A : Type'} (GEN_PVAR_155 : A -> Prop) (t : A -> Prop) (s : type686 A) : (term84 A GEN_PVAR_155 s t) = (term60 A GEN_PVAR_155 t s).
Proof. exact (MK_COMB (@lem4605423 A GEN_PVAR_155) (@lem4605422 A t s)). Qed.
Lemma lem4605425 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4605426 {A : Type'} (GEN_PVAR_155 : A -> Prop) (s : type686 A) (t : A -> Prop) : (term85 A GEN_PVAR_155 s t) = (term62 A GEN_PVAR_155 s t).
Proof. exact (MK_COMB (@lem4605424 A GEN_PVAR_155 t s) (@lem4605425 A t)). Qed.
Lemma lem4605427 {A : Type'} (GEN_PVAR_155 : A -> Prop) (s : type686 A) : (term86 A GEN_PVAR_155 s) = (term64 A GEN_PVAR_155 s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4605426 A GEN_PVAR_155 s t)). Qed.
Lemma lem4605428 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4605429 {A : Type'} (GEN_PVAR_155 : A -> Prop) (s : type686 A) : (term87 A GEN_PVAR_155 s) = (term66 A GEN_PVAR_155 s).
Proof. exact (MK_COMB (@lem4605428 A) (@lem4605427 A GEN_PVAR_155 s)). Qed.
Lemma lem4605430 {A : Type'} (s : type686 A) : (term88 A s) = (term68 A s).
Proof. exact (fun_ext (fun GEN_PVAR_155 : A -> Prop => @lem4605429 A GEN_PVAR_155 s)). Qed.
Lemma lem4605431 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4605432 {A : Type'} (s : type686 A) : (term89 A s) = (term69 A s).
Proof. exact (MK_COMB (@lem4605431 A) (@lem4605430 A s)). Qed.
Lemma lem4605433 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x) = (@IN (A -> Prop) x).
Proof. exact (eq_refl (@IN (A -> Prop) x)). Qed.
Lemma lem4605434 {A : Type'} (x : A -> Prop) (s : type686 A) : (term81 A x s) = (term71 A x s).
Proof. exact (MK_COMB (@lem4605433 A x) (@lem4605432 A s)). Qed.
Lemma lem4605435 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4605436 {A : Type'} (x : A -> Prop) (s : type686 A) : (term90 A x s) = (term91 A x s).
Proof. exact (MK_COMB (@lem4605435) (@lem4605434 A x s)). Qed.
Lemma lem4605437 {A : Type'} (x : A -> Prop) (s : type686 A) : (term82 A s x) = (term58 A x s).
Proof. exact (eq_refl (term82 A s x)). Qed.
Lemma lem4605438 {A : Type'} (x : A -> Prop) (s : type686 A) : ((term81 A x s) = (term82 A s x)) = ((term71 A x s) = (term58 A x s)).
Proof. exact (MK_COMB (@lem4605436 A x s) (@lem4605437 A x s)). Qed.
Lemma lem4605439 {A : Type'} (x : A -> Prop) (s : type686 A) : (term71 A x s) = (term58 A x s).
Proof. exact (EQ_MP (@lem4605438 A x s) (@lem4605421 A s x)). Qed.
Lemma lem4605447 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4605448 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4605447 A P x). Qed.
Lemma lem4605449 {A : Type'} (x : A -> Prop) (x' : A) : (@IN A x' x) = (x x').
Proof. exact (@lem4605448 A x x'). Qed.
Lemma lem4605450 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4605451 {A : Type'} (x : A -> Prop) (x' : A) : (term92 A x' x) = (term93 A x x').
Proof. exact (MK_COMB (@lem4605450) (@lem4605449 A x x')). Qed.
Lemma lem4605453 {A : Type'} (s : type686 A) (x : A) : (term94 A x s) = (term95 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem4605454 {A : Type'} (s : type686 A) (x : A) : (term94 A x s) = (term95 A s x).
Proof. exact (@lem4605453 A s x). Qed.
Lemma lem4605462 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4605463 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4605462 (A -> Prop) P x). Qed.
Lemma lem4605464 {A : Type'} (s : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t s) = (s t).
Proof. exact (@lem4605463 A s t). Qed.
Lemma lem4605465 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4605466 {A : Type'} (s : type686 A) (t : A -> Prop) : (term96 A t s) = (term97 A s t).
Proof. exact (MK_COMB (@lem4605465) (@lem4605464 A s t)). Qed.
Lemma lem4605468 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4605469 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4605468 A P x). Qed.
Lemma lem4605470 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4605469 A t x). Qed.
Lemma lem4605471 {A : Type'} (s : type686 A) (t : A -> Prop) (x : A) : (term98 A s x t) = (term99 A s t x).
Proof. exact (MK_COMB (@lem4605466 A s t) (@lem4605470 A t x)). Qed.
Lemma lem4605474 {A : Type'} (s : type686 A) (x : A) : (term100 A s x) = (term101 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4605471 A s t x)). Qed.
Lemma lem4605475 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4605476 {A : Type'} (s : type686 A) (x : A) : (term95 A s x) = (term102 A s x).
Proof. exact (MK_COMB (@lem4605475 A) (@lem4605474 A s x)). Qed.
Lemma lem4605481 {A : Type'} (s : type686 A) (x : A) : (term94 A x s) = (term102 A s x).
Proof. exact (TRANS (@lem4605454 A s x) (@lem4605476 A s x)). Qed.
Lemma lem4605482 {A : Type'} (x : A -> Prop) (s : type686 A) (x' : A) : (term103 A x x' s) = (term104 A x s x').
Proof. exact (MK_COMB (@lem4605451 A x x') (@lem4605481 A s x')). Qed.
Lemma lem4605485 {A : Type'} (x : A -> Prop) (s : type686 A) : (term105 A x s) = (term106 A x s).
Proof. exact (fun_ext (fun x' : A => @lem4605482 A x s x')). Qed.
Lemma lem4605486 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4605487 {A : Type'} (x : A -> Prop) (s : type686 A) : (term58 A x s) = (term107 A x s).
Proof. exact (MK_COMB (@lem4605486 A) (@lem4605485 A x s)). Qed.
Lemma lem4605492 {A : Type'} (x : A -> Prop) (s : type686 A) : (term71 A x s) = (term107 A x s).
Proof. exact (TRANS (@lem4605439 A x s) (@lem4605487 A x s)). Qed.
Lemma lem4605493 {A : Type'} (x : A -> Prop) (s : type686 A) : (term74 A x s) = (term108 A x s).
Proof. exact (MK_COMB (@lem4605417 A s x) (@lem4605492 A x s)). Qed.
Lemma lem4605496 {A : Type'} (s : type686 A) : (term76 A s) = (term109 A s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4605493 A x s)). Qed.
Lemma lem4605497 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4605498 {A : Type'} (s : type686 A) : (term77 A s) = (term110 A s).
Proof. exact (MK_COMB (@lem4605497 A) (@lem4605496 A s)). Qed.
Lemma lem4605503 {A : Type'} (s : type686 A) : (term110 A s) = (term77 A s).
Proof. exact (SYM (@lem4605498 A s)). Qed.
Lemma lem4605505 (p : Prop) : p = (term111 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4605506 {A : Type'} (s : type686 A) : (term110 A s) = (term112 A s).
Proof. exact (@lem4605505 (term110 A s)). Qed.
Lemma lem4605507 {A : Type'} (s : type686 A) : (term112 A s) = (term110 A s).
Proof. exact (SYM (@lem4605506 A s)). Qed.
Lemma lem4605508 {A : Type'} (s : type686 A) (h1 : term113 A s) : term113 A s.
Proof. exact (h1). Qed.
Lemma lem4605511 {A : Type'} (s : type686 A) (h1 : term112 A s) : term112 A s.
Proof. exact (h1). Qed.
Lemma lem4605512 {A : Type'} (s : type686 A) : term114 A s.
Proof. exact (fun h0 : term112 A s => @lem4605511 A s h0). Qed.
Lemma lem4605513 {A : Type'} (s : type686 A) (h1 : term114 A s) : term114 A s.
Proof. exact (h1). Qed.
Lemma lem4605514 {A : Type'} (s : type686 A) (h1 : term112 A s) : term112 A s.
Proof. exact (h1). Qed.
Lemma lem4605515 {A : Type'} (s : type686 A) (h1 : term112 A s) (h2 : term114 A s) : term112 A s.
Proof. exact (@lem4605513 A s h2 (@lem4605514 A s h1)). Qed.
Lemma lem4605516 {A : Type'} (s : type686 A) (h1 : term112 A s) : term115 A s.
Proof. exact (fun h0 : term114 A s => @lem4605515 A s h1 h0). Qed.
Lemma lem4605517 {A : Type'} (s : type686 A) (h1 : term114 A s) : term114 A s.
Proof. exact (h1). Qed.
Lemma lem4605518 {A : Type'} (s : type686 A) (h1 : term112 A s) (h2 : term114 A s) : term112 A s.
Proof. exact (@lem4605516 A s h1 (@lem4605517 A s h2)). Qed.
Lemma lem4605519 {A : Type'} (s : type686 A) (h1 : term114 A s) : term114 A s.
Proof. exact (fun h0 : term112 A s => @lem4605518 A s h0 h1). Qed.
Lemma lem4605520 {A : Type'} (s : type686 A) : term116 A s.
Proof. exact (fun h0 : term114 A s => @lem4605519 A s h0). Qed.
Lemma lem4605523 {A : Type'} (s : type686 A) : term114 A s.
Proof. exact (@lem4605520 A s (@lem4605512 A s)). Qed.
Lemma lem4605524 {A : Type'} (s : type686 A) : term114 A s.
Proof. exact (@lem4605523 A s). Qed.
Lemma lem4605530 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4605531 {A : Type'} (s : type686 A) : (term112 A s) = (term117 A s).
Proof. exact (@lem4605530 (term113 A s)). Qed.
Lemma lem4605533 (t : Prop) : (term118 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4605534 {A : Type'} (s : type686 A) : (term117 A s) = (term110 A s).
Proof. exact (@lem4605533 (term110 A s)). Qed.
Lemma lem4605539 {A : Type'} (s : type686 A) : (term112 A s) = (term110 A s).
Proof. exact (TRANS (@lem4605531 A s) (@lem4605534 A s)). Qed.
Lemma lem4605578 {A : Type'} : (term119 A) = (term120 A).
Proof. exact (fun_ext (fun s : type686 A => @lem4605539 A s)). Qed.
Lemma lem4605579 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4605588 {A : Type'} : (term121 A) = (term122 A).
Proof. exact (MK_COMB (@lem4605579 A) (@lem4605578 A)). Qed.
Lemma lem4605593 {A : Type'} (s : type686 A) (t : A -> Prop) (x : A) : (term99 A s t x) = (term99 A s t x).
Proof. exact (eq_refl (term99 A s t x)). Qed.
Lemma lem4605594 {A : Type'} (s : type686 A) (x : A) : (term101 A s x) = (term101 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4605593 A s t x)). Qed.
Lemma lem4605595 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4605596 {A : Type'} (s : type686 A) (x : A) : (term102 A s x) = (term102 A s x).
Proof. exact (MK_COMB (@lem4605595 A) (@lem4605594 A s x)). Qed.
Lemma lem4605599 {A : Type'} (x : A -> Prop) (x' : A) : (term93 A x x') = (term93 A x x').
Proof. exact (eq_refl (term93 A x x')). Qed.
Lemma lem4605600 {A : Type'} (x : A -> Prop) (s : type686 A) (x' : A) : (term104 A x s x') = (term104 A x s x').
Proof. exact (MK_COMB (@lem4605599 A x x') (@lem4605596 A s x')). Qed.
Lemma lem4605601 {A : Type'} (x : A -> Prop) (s : type686 A) : (term106 A x s) = (term106 A x s).
Proof. exact (fun_ext (fun x' : A => @lem4605600 A x s x')). Qed.
Lemma lem4605602 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4605603 {A : Type'} (x : A -> Prop) (s : type686 A) : (term107 A x s) = (term107 A x s).
Proof. exact (MK_COMB (@lem4605602 A) (@lem4605601 A x s)). Qed.
Lemma lem4605606 {A : Type'} (s : type686 A) (x : A -> Prop) : (term78 A s x) = (term78 A s x).
Proof. exact (eq_refl (term78 A s x)). Qed.
Lemma lem4605607 {A : Type'} (x : A -> Prop) (s : type686 A) : (term108 A x s) = (term108 A x s).
Proof. exact (MK_COMB (@lem4605606 A s x) (@lem4605603 A x s)). Qed.
Lemma lem4605608 {A : Type'} (s : type686 A) : (term109 A s) = (term109 A s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4605607 A x s)). Qed.
Lemma lem4605609 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4605610 {A : Type'} (s : type686 A) : (term110 A s) = (term110 A s).
Proof. exact (MK_COMB (@lem4605609 A) (@lem4605608 A s)). Qed.
Lemma lem4605611 {A : Type'} : (term120 A) = (term120 A).
Proof. exact (fun_ext (fun s : type686 A => @lem4605610 A s)). Qed.
Lemma lem4605612 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4605613 {A : Type'} : (term122 A) = (term122 A).
Proof. exact (MK_COMB (@lem4605612 A) (@lem4605611 A)). Qed.
Lemma lem4605646 {A : Type'} : (term121 A) = (term122 A).
Proof. exact (TRANS (@lem4605588 A) (@lem4605613 A)). Qed.
Lemma lem4605647 {A : Type'} : (term122 A) = (term121 A).
Proof. exact (SYM (@lem4605646 A)). Qed.
Lemma lem4605651 (p : Prop) : p = (term111 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4605652 {A : Type'} (s : type686 A) (x' : A) : (term102 A s x') = (term123 A s x').
Proof. exact (@lem4605651 (term102 A s x')). Qed.
Lemma lem4605653 {A : Type'} (s : type686 A) (x' : A) : (term123 A s x') = (term102 A s x').
Proof. exact (SYM (@lem4605652 A s x')). Qed.
Lemma lem4605654 {A : Type'} (s : type686 A) (x' : A) (h1 : term124 A s x') : term124 A s x'.
Proof. exact (h1). Qed.
Lemma lem4605660 {A : Type'} (s : type686 A) (x : A -> Prop) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem4605666 {A : Type'} (x : A -> Prop) (x' : A) (h1 : x x') : x x'.
Proof. exact (h1). Qed.
Lemma lem4605673 {A : Type'} (s : type686 A) (t : A -> Prop) (x' : A) : (term125 A s t x') = (term126 A s t x').
Proof. exact (@lem17045 (s t) (t x')). Qed.
Lemma lem4605674 {A : Type'} (P : type686 A) : (term127 A P) = (term128 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem4605675 {A : Type'} (s : type686 A) (x' : A) : (term124 A s x') = (term129 A s x').
Proof. exact (@lem4605674 A (term101 A s x')). Qed.
Lemma lem4605676 {A : Type'} (s : type686 A) (t : A -> Prop) (x' : A) : (term130 A s x' t) = (term99 A s t x').
Proof. exact (eq_refl (term130 A s x' t)). Qed.
Lemma lem4605677 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4605678 {A : Type'} (s : type686 A) (t : A -> Prop) (x' : A) : (term131 A s x' t) = (term125 A s t x').
Proof. exact (MK_COMB (@lem4605677) (@lem4605676 A s t x')). Qed.
Lemma lem4605679 {A : Type'} (s : type686 A) (t : A -> Prop) (x' : A) : (term131 A s x' t) = (term126 A s t x').
Proof. exact (TRANS (@lem4605678 A s t x') (@lem4605673 A s t x')). Qed.
Lemma lem4605680 {A : Type'} (s : type686 A) (x' : A) : (term132 A s x') = (term133 A s x').
Proof. exact (fun_ext (fun t : A -> Prop => @lem4605679 A s t x')). Qed.
Lemma lem4605681 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4605682 {A : Type'} (s : type686 A) (x' : A) : (term129 A s x') = (term134 A s x').
Proof. exact (MK_COMB (@lem4605681 A) (@lem4605680 A s x')). Qed.
Lemma lem4605735 {A : Type'} (s : type686 A) (x' : A) : (term124 A s x') = (term134 A s x').
Proof. exact (TRANS (@lem4605675 A s x') (@lem4605682 A s x')). Qed.
Lemma lem4605736 {A : Type'} (s : type686 A) (x' : A) (h1 : term124 A s x') : term134 A s x'.
Proof. exact (EQ_MP (@lem4605735 A s x') (@lem4605654 A s x' h1)). Qed.
Lemma lem4605741 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4605742 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4605741 (A -> Prop) Prop f x). Qed.
Lemma lem4605744 {A : Type'} (s : type686 A) (x : A -> Prop) : (s x) = (@I ((A -> Prop) -> Prop) s x).
Proof. exact (@lem4605742 A s x). Qed.
Lemma lem4605750 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4605751 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4605750 A Prop f x). Qed.
Lemma lem4605753 {A : Type'} (x : A -> Prop) (x' : A) : (x x') = (@I (A -> Prop) x x').
Proof. exact (@lem4605751 A x x'). Qed.
Lemma lem4605755 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4605760 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4605761 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4605760 A Prop f x). Qed.
Lemma lem4605763 {A : Type'} (t : A -> Prop) (x' : A) : (t x') = (@I (A -> Prop) t x').
Proof. exact (@lem4605761 A t x'). Qed.
Lemma lem4605764 {A : Type'} (t : A -> Prop) (x' : A) : (term135 A t x') = (term136 A t x').
Proof. exact (MK_COMB (@lem4605755) (@lem4605763 A t x')). Qed.
Lemma lem4605765 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4605770 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4605771 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4605770 (A -> Prop) Prop f x). Qed.
Lemma lem4605773 {A : Type'} (s : type686 A) (t : A -> Prop) : (s t) = (@I ((A -> Prop) -> Prop) s t).
Proof. exact (@lem4605771 A s t). Qed.
Lemma lem4605774 {A : Type'} (s : type686 A) (t : A -> Prop) : (term137 A s t) = (term138 A s t).
Proof. exact (MK_COMB (@lem4605765) (@lem4605773 A s t)). Qed.
Lemma lem4605775 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4605776 {A : Type'} (s : type686 A) (t : A -> Prop) : (term139 A s t) = (term140 A s t).
Proof. exact (MK_COMB (@lem4605775) (@lem4605774 A s t)). Qed.
Lemma lem4605777 {A : Type'} (s : type686 A) (t : A -> Prop) (x' : A) : (term126 A s t x') = (term141 A s t x').
Proof. exact (MK_COMB (@lem4605776 A s t) (@lem4605764 A t x')). Qed.
Lemma lem4605778 {A : Type'} (s : type686 A) (x' : A) : (term133 A s x') = (term142 A s x').
Proof. exact (fun_ext (fun t : A -> Prop => @lem4605777 A s t x')). Qed.
Lemma lem4605779 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4605780 {A : Type'} (s : type686 A) (x' : A) : (term134 A s x') = (term143 A s x').
Proof. exact (MK_COMB (@lem4605779 A) (@lem4605778 A s x')). Qed.
Lemma lem4605781 {A : Type'} (s : type686 A) (x' : A) (h1 : term124 A s x') : term143 A s x'.
Proof. exact (EQ_MP (@lem4605780 A s x') (@lem4605736 A s x' h1)). Qed.
Lemma lem4605797 {A : Type'} (s : type686 A) (t : A -> Prop) (x' : A) : (term141 A s t x') = (term141 A s t x').
Proof. exact (eq_refl (term141 A s t x')). Qed.
Lemma lem4605798 {A : Type'} (s : type686 A) (x' : A) : (term142 A s x') = (term142 A s x').
Proof. exact (fun_ext (fun t : A -> Prop => @lem4605797 A s t x')). Qed.
Lemma lem4605799 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4605801 {A : Type'} (s : type686 A) (x' : A) : (term143 A s x') = (term143 A s x').
Proof. exact (MK_COMB (@lem4605799 A) (@lem4605798 A s x')). Qed.
Lemma lem4605802 {A : Type'} (s : type686 A) (x' : A) (h1 : term124 A s x') : term143 A s x'.
Proof. exact (EQ_MP (@lem4605801 A s x') (@lem4605781 A s x' h1)). Qed.
Lemma lem4605803 {A : Type'} (_55360 : A -> Prop) (s : type686 A) (x' : A) (h1 : term124 A s x') : term144 A s x' _55360.
Proof. exact (@lem4605802 A s x' h1 _55360). Qed.
Lemma lem4605804 {A : Type'} (s : type686 A) (_55360 : A -> Prop) (x' : A) : (term144 A s x' _55360) = (term141 A s _55360 x').
Proof. exact (eq_refl (term144 A s x' _55360)). Qed.
Lemma lem4605815 {A : Type'} (_55360 : A -> Prop) (s : type686 A) (x' : A) (h1 : term124 A s x') : term141 A s _55360 x'.
Proof. exact (EQ_MP (@lem4605804 A s _55360 x') (@lem4605803 A _55360 s x' h1)). Qed.
Lemma lem4605817 {A : Type'} (s : type686 A) (x : A -> Prop) (h1 : s x) : @I ((A -> Prop) -> Prop) s x.
Proof. exact (EQ_MP (@lem4605744 A s x) (@lem4605660 A s x h1)). Qed.
Lemma lem4605818 {A : Type'} (s : type686 A) (x : A -> Prop) (h1 : s x) : term145 A s x.
Proof. exact (fun h0 : term138 A s x => @lem4605817 A s x h1). Qed.
Lemma lem4605820 (p : Prop) : (term146 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4605821 {A : Type'} (s : type686 A) (x : A -> Prop) : (term145 A s x) = (@I ((A -> Prop) -> Prop) s x).
Proof. exact (@lem4605820 (@I ((A -> Prop) -> Prop) s x)). Qed.
Lemma lem4605822 {A : Type'} (s : type686 A) (x : A -> Prop) (h1 : s x) : @I ((A -> Prop) -> Prop) s x.
Proof. exact (EQ_MP (@lem4605821 A s x) (@lem4605818 A s x h1)). Qed.
Lemma lem4605824 {A : Type'} (x : A -> Prop) (x' : A) (h1 : x x') : @I (A -> Prop) x x'.
Proof. exact (EQ_MP (@lem4605753 A x x') (@lem4605666 A x x' h1)). Qed.
Lemma lem4605825 {A : Type'} (x : A -> Prop) (x' : A) (h1 : x x') : term147 A x x'.
Proof. exact (fun h0 : term136 A x x' => @lem4605824 A x x' h1). Qed.
Lemma lem4605827 (p : Prop) : (term146 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4605828 {A : Type'} (x : A -> Prop) (x' : A) : (term147 A x x') = (@I (A -> Prop) x x').
Proof. exact (@lem4605827 (@I (A -> Prop) x x')). Qed.
Lemma lem4605829 {A : Type'} (x : A -> Prop) (x' : A) (h1 : x x') : @I (A -> Prop) x x'.
Proof. exact (EQ_MP (@lem4605828 A x x') (@lem4605825 A x x' h1)). Qed.
Lemma lem4605831 (a : Prop) (b : Prop) : (term148 a b) = (term149 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4605832 {A : Type'} (s : type686 A) (_55360 : A -> Prop) (x' : A) : (term141 A s _55360 x') = (term150 A s _55360 x').
Proof. exact (@lem4605831 (@I ((A -> Prop) -> Prop) s _55360) (@I (A -> Prop) _55360 x')). Qed.
Lemma lem4605834 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4605835 {A : Type'} (s : type686 A) (_55360 : A -> Prop) (x' : A) : (term150 A s _55360 x') = (term151 A s _55360 x').
Proof. exact (@lem4605834 (term152 A s _55360 x')). Qed.
Lemma lem4605836 {A : Type'} (s : type686 A) (_55360 : A -> Prop) (x' : A) : (term141 A s _55360 x') = (term151 A s _55360 x').
Proof. exact (TRANS (@lem4605832 A s _55360 x') (@lem4605835 A s _55360 x')). Qed.
Lemma lem4605838 {A : Type'} (s : type686 A) (x : A -> Prop) (x' : A) (h1 : s x) (h2 : x x') : term152 A s x x'.
Proof. exact (conj (@lem4605822 A s x h1) (@lem4605829 A x x' h2)). Qed.
Lemma lem4605840 {A : Type'} (_55360 : A -> Prop) (s : type686 A) (x' : A) (h1 : term124 A s x') : term151 A s _55360 x'.
Proof. exact (EQ_MP (@lem4605836 A s _55360 x') (@lem4605815 A _55360 s x' h1)). Qed.
Lemma lem4605841 {A : Type'} (_55360 : A -> Prop) (s : type686 A) (x' : A) (h1 : term124 A s x') : term151 A s _55360 x'.
Proof. exact (@lem4605840 A _55360 s x' h1). Qed.
Lemma lem4605842 {A : Type'} (x : A -> Prop) (s : type686 A) (x' : A) (h1 : term124 A s x') : term151 A s x x'.
Proof. exact (@lem4605841 A x s x' h1). Qed.
Lemma lem4605845 {A : Type'} (s : type686 A) (x : A -> Prop) (x' : A) (h1 : term124 A s x') (h2 : s x) (h3 : x x') : False.
Proof. exact (@lem4605842 A x s x' h1 (@lem4605838 A s x x' h2 h3)). Qed.
Lemma lem4605846 {A : Type'} (s : type686 A) (x : A -> Prop) (x' : A) (h1 : term124 A s x') (h2 : s x) (h3 : x x') : term153.
Proof. exact (fun h0 : ~ False => @lem4605845 A s x x' h1 h2 h3). Qed.
Lemma lem4605848 (p : Prop) : (term146 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4605849 : term153 = False.
Proof. exact (@lem4605848 False). Qed.
Lemma lem4605850 {A : Type'} (s : type686 A) (x : A -> Prop) (x' : A) (h1 : term124 A s x') (h2 : s x) (h3 : x x') : False.
Proof. exact (EQ_MP (@lem4605849) (@lem4605846 A s x x' h1 h2 h3)). Qed.
Lemma lem4605851 {A : Type'} (s : type686 A) (x : A -> Prop) (x' : A) (h1 : term124 A s x') (h2 : s x) (h3 : x x') : (x x') = False.
Proof. exact (prop_ext (fun h4 : x x' => @lem4605850 A s x x' h1 h2 h3) (fun h4 : False => @lem4605666 A x x' h3)). Qed.
Lemma lem4605852 {A : Type'} (s : type686 A) (x : A -> Prop) (x' : A) (h1 : term124 A s x') (h2 : s x) (h3 : x x') : False.
Proof. exact (EQ_MP (@lem4605851 A s x x' h1 h2 h3) (@lem4605666 A x x' h3)). Qed.
Lemma lem4605853 {A : Type'} (s : type686 A) (x : A -> Prop) (x' : A) (h1 : term124 A s x') (h2 : s x) (h3 : x x') : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem4605852 A s x x' h1 h2 h3) (fun h4 : False => @lem4605660 A s x h2)). Qed.
Lemma lem4605854 {A : Type'} (s : type686 A) (x : A -> Prop) (x' : A) (h1 : term124 A s x') (h2 : s x) (h3 : x x') : False.
Proof. exact (EQ_MP (@lem4605853 A s x x' h1 h2 h3) (@lem4605660 A s x h2)). Qed.
Lemma lem4605855 {A : Type'} (s : type686 A) (x : A -> Prop) (x' : A) (h1 : term124 A s x') (h2 : s x) (h3 : x x') : (term124 A s x') = False.
Proof. exact (prop_ext (fun h4 : term124 A s x' => @lem4605854 A s x x' h1 h2 h3) (fun h4 : False => @lem4605654 A s x' h1)). Qed.
Lemma lem4605856 {A : Type'} (s : type686 A) (x : A -> Prop) (x' : A) (h1 : term124 A s x') (h2 : s x) (h3 : x x') : False.
Proof. exact (EQ_MP (@lem4605855 A s x x' h1 h2 h3) (@lem4605654 A s x' h1)). Qed.
Lemma lem4605857 {A : Type'} (s : type686 A) (x : A -> Prop) (x' : A) (h1 : s x) (h2 : x x') : term123 A s x'.
Proof. exact (fun h0 : term124 A s x' => @lem4605856 A s x x' h0 h1 h2). Qed.
Lemma lem4605858 {A : Type'} (s : type686 A) (x : A -> Prop) (x' : A) (h1 : s x) (h2 : x x') : term102 A s x'.
Proof. exact (EQ_MP (@lem4605653 A s x') (@lem4605857 A s x x' h1 h2)). Qed.
Lemma lem4605859 {A : Type'} (x' : A) (s : type686 A) (x : A -> Prop) (h1 : s x) : term104 A x s x'.
Proof. exact (fun h0 : x x' => @lem4605858 A s x x' h1 h0). Qed.
Lemma lem4605864 {A : Type'} (s : type686 A) (x : A -> Prop) (h1 : s x) : term107 A x s.
Proof. exact (fun x' : A => @lem4605859 A x' s x h1). Qed.
Lemma lem4605865 {A : Type'} (x : A -> Prop) (s : type686 A) : term108 A x s.
Proof. exact (fun h0 : s x => @lem4605864 A s x h0). Qed.
Lemma lem4605870 {A : Type'} (s : type686 A) : term110 A s.
Proof. exact (fun x : A -> Prop => @lem4605865 A x s). Qed.
Lemma lem4605875 {A : Type'} : term122 A.
Proof. exact (fun s : type686 A => @lem4605870 A s). Qed.
Lemma lem4605876 {A : Type'} : term121 A.
Proof. exact (EQ_MP (@lem4605647 A) (@lem4605875 A)). Qed.
Lemma lem4605877 {A : Type'} (s : type686 A) : term154 A s.
Proof. exact (@lem4605876 A s). Qed.
Lemma lem4605878 {A : Type'} (s : type686 A) : (term154 A s) = (term112 A s).
Proof. exact (eq_refl (term154 A s)). Qed.
Lemma lem4605879 {A : Type'} (s : type686 A) : term112 A s.
Proof. exact (EQ_MP (@lem4605878 A s) (@lem4605877 A s)). Qed.
Lemma lem4605881 {A : Type'} (s : type686 A) : term112 A s.
Proof. exact (@lem4605524 A s (@lem4605879 A s)). Qed.
Lemma lem4605882 {A : Type'} (s : type686 A) (h1 : term113 A s) : False.
Proof. exact (@lem4605881 A s (@lem4605508 A s h1)). Qed.
Lemma lem4605883 {A : Type'} (s : type686 A) (h1 : term113 A s) : (term113 A s) = False.
Proof. exact (prop_ext (fun h2 : term113 A s => @lem4605882 A s h1) (fun h2 : False => @lem4605508 A s h1)). Qed.
Lemma lem4605884 {A : Type'} (s : type686 A) (h1 : term113 A s) : False.
Proof. exact (EQ_MP (@lem4605883 A s h1) (@lem4605508 A s h1)). Qed.
Lemma lem4605885 {A : Type'} (s : type686 A) : term112 A s.
Proof. exact (fun h0 : term113 A s => @lem4605884 A s h0). Qed.
Lemma lem4605886 {A : Type'} (s : type686 A) : term110 A s.
Proof. exact (EQ_MP (@lem4605507 A s) (@lem4605885 A s)). Qed.
Lemma lem4605887 {A : Type'} (s : type686 A) : term77 A s.
Proof. exact (EQ_MP (@lem4605503 A s) (@lem4605886 A s)). Qed.
Lemma lem4605888 {A : Type'} (s : type686 A) : term55 A s.
Proof. exact (EQ_MP (@lem4605405 A s) (@lem4605887 A s)). Qed.
Lemma lem4605889 {A : Type'} (s : type686 A) : term49 A s.
Proof. exact (@lem4605352 A s (@lem4605888 A s)). Qed.
Lemma lem4605890 {A : Type'} (s : type686 A) : term47 A s.
Proof. exact (EQ_MP (@lem4605348 A s) (@lem4605889 A s)). Qed.
Lemma lem4605891 {A : Type'} (s : type686 A) (h1 : term29 A s) : term44 A s.
Proof. exact (@lem4605890 A s (@lem4605096 A s h1)). Qed.
Lemma lem4605892 {A : Type'} (s : type686 A) (h1 : term32 A s) (h2 : term29 A s) : False.
Proof. exact (@lem4605891 A s h2 (@lem4605326 A s h1)). Qed.
Lemma lem4605893 {A : Type'} (s : type686 A) (h1 : term29 A s) : term155 A s.
Proof. exact (fun h0 : term32 A s => @lem4605892 A s h0 h1). Qed.
Lemma lem4605894 {A : Type'} (s : type686 A) : (term155 A s) = (term41 A s).
Proof. exact (@lem69 (term32 A s)). Qed.
Lemma lem4605895 {A : Type'} (s : type686 A) (h1 : term29 A s) : term41 A s.
Proof. exact (EQ_MP (@lem4605894 A s) (@lem4605893 A s h1)). Qed.
Lemma lem4605896 {A : Type'} (s : type686 A) (h1 : term29 A s) : (term32 A s) = (term37 A s).
Proof. exact (EQ_MP (@lem4605320 A s h1) (@lem4605895 A s h1)). Qed.
Lemma lem4605897 {A : Type'} (s : type686 A) : (term32 A s) = (term37 A s).
Proof. exact (or_elim (@lem4605094 A s) (fun h0 : @FINITE (A -> Prop) s => @lem4605248 A s h0) (fun h0 : term29 A s => @lem4605896 A s h0)). Qed.
Lemma lem4605902 {A : Type'} : term156 A.
Proof. exact (fun s : type686 A => @lem4605897 A s). Qed.
