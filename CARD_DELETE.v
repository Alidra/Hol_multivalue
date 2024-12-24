Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_DELETE_term_abbrevs.
Require Import CARD_CLAUSES_spec.
Require Import FINITE_DELETE_spec.
Require Import IN_DELETE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import SUC_SUB1_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm13473_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm7_spec.
Lemma lem3843883 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3843884 (_474 : nat) (_475 : Prop) (_476 : nat -> Prop) (_477 : nat) : (term0 _476 _475 _474 _477) = (term1 _474 _475 _476 _477).
Proof. exact (@lem13473 nat _474 _475 _476 _477). Qed.
Lemma lem3843885 {A : Type'} (_474 : nat) (_475 : Prop) (s : A -> Prop) (x : A) (_477 : nat) : (term2 A s x _475 _474 _477) = (term3 A _474 _475 s x _477).
Proof. exact (@lem3843884 _474 _475 (term4 A s x) _477). Qed.
Lemma lem3843886 {A : Type'} (x : A) (s : A -> Prop) : (term5 A x s) = (term6 A x s).
Proof. exact (@lem3843885 A (term7 A s) (@IN A x s) s x (@CARD A s)). Qed.
Lemma lem3843887 {A : Type'} (x : A) (s : A -> Prop) : (term8 A x s) = ((term9 A s x) = (@CARD A s)).
Proof. exact (eq_refl (term8 A x s)). Qed.
Lemma lem3843888 {A : Type'} (x : A) (s : A -> Prop) : (term10 A x s) = (term10 A x s).
Proof. exact (eq_refl (term10 A x s)). Qed.
Lemma lem3843889 {A : Type'} (x : A) (s : A -> Prop) : (term11 A x s) = (term12 A x s).
Proof. exact (MK_COMB (@lem3843888 A x s) (@lem3843887 A x s)). Qed.
Lemma lem3843890 {A : Type'} (x : A) (s : A -> Prop) : (term13 A x s) = ((term9 A s x) = (term7 A s)).
Proof. exact (eq_refl (term13 A x s)). Qed.
Lemma lem3843891 {A : Type'} (x : A) (s : A -> Prop) : (term14 A x s) = (term14 A x s).
Proof. exact (eq_refl (term14 A x s)). Qed.
Lemma lem3843892 {A : Type'} (x : A) (s : A -> Prop) : (term15 A x s) = (term16 A x s).
Proof. exact (MK_COMB (@lem3843891 A x s) (@lem3843890 A x s)). Qed.
Lemma lem3843893 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3843894 {A : Type'} (x : A) (s : A -> Prop) : (term17 A x s) = (term18 A x s).
Proof. exact (MK_COMB (@lem3843893) (@lem3843892 A x s)). Qed.
Lemma lem3843895 {A : Type'} (x : A) (s : A -> Prop) : (term6 A x s) = (term19 A x s).
Proof. exact (MK_COMB (@lem3843894 A x s) (@lem3843889 A x s)). Qed.
Lemma lem3843896 {A : Type'} (x : A) (s : A -> Prop) : (term5 A x s) = ((term9 A s x) = (term20 A x s)).
Proof. exact (eq_refl (term5 A x s)). Qed.
Lemma lem3843897 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3843898 {A : Type'} (x : A) (s : A -> Prop) : (term21 A x s) = (term22 A x s).
Proof. exact (MK_COMB (@lem3843897) (@lem3843896 A x s)). Qed.
Lemma lem3843899 {A : Type'} (x : A) (s : A -> Prop) : ((term5 A x s) = (term6 A x s)) = (((term9 A s x) = (term20 A x s)) = (term19 A x s)).
Proof. exact (MK_COMB (@lem3843898 A x s) (@lem3843895 A x s)). Qed.
Lemma lem3843900 {A : Type'} (x : A) (s : A -> Prop) : ((term9 A s x) = (term20 A x s)) = (term19 A x s).
Proof. exact (EQ_MP (@lem3843899 A x s) (@lem3843886 A x s)). Qed.
Lemma lem3843901 {A : Type'} (x : A) (s : A -> Prop) : (term19 A x s) = ((term9 A s x) = (term20 A x s)).
Proof. exact (SYM (@lem3843900 A x s)). Qed.
Lemma lem3843902 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem3843919 {A : Type'} (x : A) (s : A -> Prop) (h1 : term23 A x s) : term23 A x s.
Proof. exact (h1). Qed.
Lemma lem3843938 {A : Type'} (s : A -> Prop) (x : A) (h1 : s = (term24 A s x)) : s = (term24 A s x).
Proof. exact (h1). Qed.
Lemma lem3843939 {A : Type'} : (@CARD A) = (@CARD A).
Proof. exact (eq_refl (@CARD A)). Qed.
Lemma lem3843940 {A : Type'} (s : A -> Prop) (x : A) (h1 : s = (term24 A s x)) : (@CARD A s) = (term25 A s x).
Proof. exact (MK_COMB (@lem3843939 A) (@lem3843938 A s x h1)). Qed.
Lemma lem3843941 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem3843942 {A : Type'} (s : A -> Prop) (x : A) (h1 : s = (term24 A s x)) : (term26 A s) = (term27 A s x).
Proof. exact (MK_COMB (@lem3843941) (@lem3843940 A s x h1)). Qed.
Lemma lem3843943 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem3843944 {A : Type'} (s : A -> Prop) (x : A) (h1 : s = (term24 A s x)) : (term7 A s) = (term29 A s x).
Proof. exact (MK_COMB (@lem3843942 A s x h1) (@lem3843943)). Qed.
Lemma lem3843945 {A : Type'} (s : A -> Prop) (x : A) : (term30 A s x) = (term30 A s x).
Proof. exact (eq_refl (term30 A s x)). Qed.
Lemma lem3843946 {A : Type'} (s : A -> Prop) (x : A) (h1 : s = (term24 A s x)) : ((term9 A s x) = (term7 A s)) = ((term9 A s x) = (term29 A s x)).
Proof. exact (MK_COMB (@lem3843945 A s x) (@lem3843944 A s x h1)). Qed.
Lemma lem3843947 {A : Type'} (s : A -> Prop) (x : A) (h1 : s = (term24 A s x)) : ((term9 A s x) = (term29 A s x)) = ((term9 A s x) = (term7 A s)).
Proof. exact (SYM (@lem3843946 A s x h1)). Qed.
Lemma lem3843953 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term31 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3843954 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term31 A s t).
Proof. exact (@lem3843953 A s t). Qed.
Lemma lem3843955 {A : Type'} (s : A -> Prop) (x : A) : (s = (term24 A s x)) = (term32 A s x).
Proof. exact (@lem3843954 A s (term24 A s x)). Qed.
Lemma lem3843964 {A : Type'} (x : A) (s : A -> Prop) : (term14 A x s) = (term14 A x s).
Proof. exact (eq_refl (term14 A x s)). Qed.
Lemma lem3843965 {A : Type'} (s : A -> Prop) (x : A) : (term33 A s x) = (term34 A s x).
Proof. exact (MK_COMB (@lem3843964 A x s) (@lem3843955 A s x)). Qed.
Lemma lem3843968 {A : Type'} (s : A -> Prop) (x : A) : (term34 A s x) = (term33 A s x).
Proof. exact (SYM (@lem3843965 A s x)). Qed.
Lemma lem3843972 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3843973 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3843972 A P x). Qed.
Lemma lem3843974 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3843973 A s x). Qed.
Lemma lem3843975 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3843976 {A : Type'} (s : A -> Prop) (x : A) : (term14 A x s) = (term35 A s x).
Proof. exact (MK_COMB (@lem3843975) (@lem3843974 A s x)). Qed.
Lemma lem3843984 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3843985 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3843984 A P x). Qed.
Lemma lem3843986 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3843985 A s x'). Qed.
Lemma lem3843987 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3843988 {A : Type'} (s : A -> Prop) (x' : A) : (term36 A x' s) = (term37 A s x').
Proof. exact (MK_COMB (@lem3843987) (@lem3843986 A s x')). Qed.
Lemma lem3843990 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term38 A x y s) = (term39 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3843991 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term38 A x y s) = (term39 A y x s).
Proof. exact (@lem3843990 A y x s). Qed.
Lemma lem3843992 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : (term40 A x' s x) = (term41 A x' s x).
Proof. exact (@lem3843991 A x x' (@DELETE A s x)). Qed.
Lemma lem3843998 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term42 A x s y) = (term43 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3843999 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term42 A x s y) = (term43 A s x y).
Proof. exact (@lem3843998 A s x y). Qed.
Lemma lem3844000 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term42 A x' s x) = (term43 A s x' x).
Proof. exact (@lem3843999 A s x' x). Qed.
Lemma lem3844004 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3844005 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3844004 A P x). Qed.
Lemma lem3844006 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3844005 A s x'). Qed.
Lemma lem3844007 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3844008 {A : Type'} (s : A -> Prop) (x' : A) : (term44 A x' s) = (term45 A s x').
Proof. exact (MK_COMB (@lem3844007) (@lem3844006 A s x')). Qed.
Lemma lem3844011 {A : Type'} (x' : A) (x : A) : (term46 A x' x) = (term46 A x' x).
Proof. exact (eq_refl (term46 A x' x)). Qed.
Lemma lem3844012 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term43 A s x' x) = (term47 A s x' x).
Proof. exact (MK_COMB (@lem3844008 A s x') (@lem3844011 A x' x)). Qed.
Lemma lem3844015 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term42 A x' s x) = (term47 A s x' x).
Proof. exact (TRANS (@lem3844000 A s x' x) (@lem3844012 A s x' x)). Qed.
Lemma lem3844016 {A : Type'} (x' : A) (x : A) : (term48 A x' x) = (term48 A x' x).
Proof. exact (eq_refl (term48 A x' x)). Qed.
Lemma lem3844017 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term41 A x' s x) = (term49 A s x' x).
Proof. exact (MK_COMB (@lem3844016 A x' x) (@lem3844015 A s x' x)). Qed.
Lemma lem3844020 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term40 A x' s x) = (term49 A s x' x).
Proof. exact (TRANS (@lem3843992 A x' s x) (@lem3844017 A s x' x)). Qed.
Lemma lem3844021 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : ((@IN A x' s) = (term40 A x' s x)) = ((s x') = (term49 A s x' x)).
Proof. exact (MK_COMB (@lem3843988 A s x') (@lem3844020 A s x' x)). Qed.
Lemma lem3844024 {A : Type'} (s : A -> Prop) (x : A) : (term50 A s x) = (term51 A s x).
Proof. exact (fun_ext (fun x' : A => @lem3844021 A s x' x)). Qed.
Lemma lem3844025 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3844026 {A : Type'} (s : A -> Prop) (x : A) : (term32 A s x) = (term52 A s x).
Proof. exact (MK_COMB (@lem3844025 A) (@lem3844024 A s x)). Qed.
Lemma lem3844031 {A : Type'} (s : A -> Prop) (x : A) : (term34 A s x) = (term53 A s x).
Proof. exact (MK_COMB (@lem3843976 A s x) (@lem3844026 A s x)). Qed.
Lemma lem3844034 {A : Type'} (s : A -> Prop) (x : A) : (term53 A s x) = (term34 A s x).
Proof. exact (SYM (@lem3844031 A s x)). Qed.
Lemma lem3844036 (p : Prop) : p = (term54 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3844037 {A : Type'} (s : A -> Prop) (x : A) : (term53 A s x) = (term55 A s x).
Proof. exact (@lem3844036 (term53 A s x)). Qed.
Lemma lem3844038 {A : Type'} (s : A -> Prop) (x : A) : (term55 A s x) = (term53 A s x).
Proof. exact (SYM (@lem3844037 A s x)). Qed.
Lemma lem3844039 {A : Type'} (s : A -> Prop) (x : A) (h1 : term56 A s x) : term56 A s x.
Proof. exact (h1). Qed.
Lemma lem3844042 {A : Type'} (s : A -> Prop) (x : A) (h1 : term55 A s x) : term55 A s x.
Proof. exact (h1). Qed.
Lemma lem3844043 {A : Type'} (s : A -> Prop) (x : A) : term57 A s x.
Proof. exact (fun h0 : term55 A s x => @lem3844042 A s x h0). Qed.
Lemma lem3844044 {A : Type'} (s : A -> Prop) (x : A) (h1 : term57 A s x) : term57 A s x.
Proof. exact (h1). Qed.
Lemma lem3844045 {A : Type'} (s : A -> Prop) (x : A) (h1 : term55 A s x) : term55 A s x.
Proof. exact (h1). Qed.
Lemma lem3844046 {A : Type'} (s : A -> Prop) (x : A) (h1 : term55 A s x) (h2 : term57 A s x) : term55 A s x.
Proof. exact (@lem3844044 A s x h2 (@lem3844045 A s x h1)). Qed.
Lemma lem3844047 {A : Type'} (s : A -> Prop) (x : A) (h1 : term55 A s x) : term58 A s x.
Proof. exact (fun h0 : term57 A s x => @lem3844046 A s x h1 h0). Qed.
Lemma lem3844048 {A : Type'} (s : A -> Prop) (x : A) (h1 : term57 A s x) : term57 A s x.
Proof. exact (h1). Qed.
Lemma lem3844049 {A : Type'} (s : A -> Prop) (x : A) (h1 : term55 A s x) (h2 : term57 A s x) : term55 A s x.
Proof. exact (@lem3844047 A s x h1 (@lem3844048 A s x h2)). Qed.
Lemma lem3844050 {A : Type'} (s : A -> Prop) (x : A) (h1 : term57 A s x) : term57 A s x.
Proof. exact (fun h0 : term55 A s x => @lem3844049 A s x h0 h1). Qed.
Lemma lem3844051 {A : Type'} (s : A -> Prop) (x : A) : term59 A s x.
Proof. exact (fun h0 : term57 A s x => @lem3844050 A s x h0). Qed.
Lemma lem3844054 {A : Type'} (s : A -> Prop) (x : A) : term57 A s x.
Proof. exact (@lem3844051 A s x (@lem3844043 A s x)). Qed.
Lemma lem3844055 {A : Type'} (s : A -> Prop) (x : A) : term57 A s x.
Proof. exact (@lem3844054 A s x). Qed.
Lemma lem3844065 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3844066 {A : Type'} (s : A -> Prop) (x : A) : (term55 A s x) = (term60 A s x).
Proof. exact (@lem3844065 (term56 A s x)). Qed.
Lemma lem3844068 (t : Prop) : (term61 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3844069 {A : Type'} (s : A -> Prop) (x : A) : (term60 A s x) = (term53 A s x).
Proof. exact (@lem3844068 (term53 A s x)). Qed.
Lemma lem3844072 {A : Type'} (s : A -> Prop) (x : A) : (term55 A s x) = (term53 A s x).
Proof. exact (TRANS (@lem3844066 A s x) (@lem3844069 A s x)). Qed.
Lemma lem3844081 {A : Type'} (x : A) : (term62 A x) = (term63 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3844072 A s x)). Qed.
Lemma lem3844082 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3844083 {A : Type'} (x : A) : (term64 A x) = (term65 A x).
Proof. exact (MK_COMB (@lem3844082 A) (@lem3844081 A x)). Qed.
Lemma lem3844088 {A : Type'} : (term66 A) = (term67 A).
Proof. exact (fun_ext (fun x : A => @lem3844083 A x)). Qed.
Lemma lem3844089 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3844098 {A : Type'} : (term68 A) = (term69 A).
Proof. exact (MK_COMB (@lem3844089 A) (@lem3844088 A)). Qed.
Lemma lem3844113 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : ((s x') = (term49 A s x' x)) = ((s x') = (term49 A s x' x)).
Proof. exact (eq_refl ((s x') = (term49 A s x' x))). Qed.
Lemma lem3844114 {A : Type'} (s : A -> Prop) (x : A) : (term51 A s x) = (term51 A s x).
Proof. exact (fun_ext (fun x' : A => @lem3844113 A s x' x)). Qed.
Lemma lem3844115 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3844116 {A : Type'} (s : A -> Prop) (x : A) : (term52 A s x) = (term52 A s x).
Proof. exact (MK_COMB (@lem3844115 A) (@lem3844114 A s x)). Qed.
Lemma lem3844119 {A : Type'} (s : A -> Prop) (x : A) : (term35 A s x) = (term35 A s x).
Proof. exact (eq_refl (term35 A s x)). Qed.
Lemma lem3844120 {A : Type'} (s : A -> Prop) (x : A) : (term53 A s x) = (term53 A s x).
Proof. exact (MK_COMB (@lem3844119 A s x) (@lem3844116 A s x)). Qed.
Lemma lem3844121 {A : Type'} (x : A) : (term63 A x) = (term63 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3844120 A s x)). Qed.
Lemma lem3844122 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3844123 {A : Type'} (x : A) : (term65 A x) = (term65 A x).
Proof. exact (MK_COMB (@lem3844122 A) (@lem3844121 A x)). Qed.
Lemma lem3844124 {A : Type'} : (term67 A) = (term67 A).
Proof. exact (fun_ext (fun x : A => @lem3844123 A x)). Qed.
Lemma lem3844125 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3844126 {A : Type'} : (term69 A) = (term69 A).
Proof. exact (MK_COMB (@lem3844125 A) (@lem3844124 A)). Qed.
Lemma lem3844153 {A : Type'} : (term68 A) = (term69 A).
Proof. exact (TRANS (@lem3844098 A) (@lem3844126 A)). Qed.
Lemma lem3844154 {A : Type'} : (term69 A) = (term68 A).
Proof. exact (SYM (@lem3844153 A)). Qed.
Lemma lem3844157 (p : Prop) : p = (term54 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3844158 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : ((s x') = (term49 A s x' x)) = (term70 A s x' x).
Proof. exact (@lem3844157 ((s x') = (term49 A s x' x))). Qed.
Lemma lem3844159 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term70 A s x' x) = ((s x') = (term49 A s x' x)).
Proof. exact (SYM (@lem3844158 A s x' x)). Qed.
Lemma lem3844160 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term71 A s x' x) : term71 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3844166 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3844176 {A : Type'} (x' : A) (x : A) : (term72 A x' x) = (x' = x).
Proof. exact (@lem16933 (x' = x)). Qed.
Lemma lem3844178 {A : Type'} (s : A -> Prop) (x' : A) : (term73 A s x') = (term73 A s x').
Proof. exact (eq_refl (term73 A s x')). Qed.
Lemma lem3844179 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term74 A s x' x) = (term75 A s x' x).
Proof. exact (MK_COMB (@lem3844178 A s x') (@lem3844176 A x' x)). Qed.
Lemma lem3844180 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term76 A s x' x) = (term74 A s x' x).
Proof. exact (@lem17045 (s x') (term46 A x' x)). Qed.
Lemma lem3844181 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term76 A s x' x) = (term75 A s x' x).
Proof. exact (TRANS (@lem3844180 A s x' x) (@lem3844179 A s x' x)). Qed.
Lemma lem3844186 {A : Type'} (x' : A) (x : A) : (term77 A x' x) = (term77 A x' x).
Proof. exact (eq_refl (term77 A x' x)). Qed.
Lemma lem3844187 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term78 A s x' x) = (term79 A s x' x).
Proof. exact (MK_COMB (@lem3844186 A x' x) (@lem3844181 A s x' x)). Qed.
Lemma lem3844188 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term80 A s x' x) = (term78 A s x' x).
Proof. exact (@lem17160 (x' = x) (term47 A s x' x)). Qed.
Lemma lem3844189 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term80 A s x' x) = (term79 A s x' x).
Proof. exact (TRANS (@lem3844188 A s x' x) (@lem3844187 A s x' x)). Qed.
Lemma lem3844195 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term81 A s x' x) = (term81 A s x' x).
Proof. exact (eq_refl (term81 A s x' x)). Qed.
Lemma lem3844197 {A : Type'} (s : A -> Prop) (x' : A) : (term45 A s x') = (term45 A s x').
Proof. exact (eq_refl (term45 A s x')). Qed.
Lemma lem3844198 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term82 A s x' x) = (term83 A s x' x).
Proof. exact (MK_COMB (@lem3844197 A s x') (@lem3844189 A s x' x)). Qed.
Lemma lem3844199 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3844200 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term84 A s x' x) = (term85 A s x' x).
Proof. exact (MK_COMB (@lem3844199) (@lem3844198 A s x' x)). Qed.
Lemma lem3844201 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term86 A s x' x) = (term87 A s x' x).
Proof. exact (MK_COMB (@lem3844200 A s x' x) (@lem3844195 A s x' x)). Qed.
Lemma lem3844202 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term71 A s x' x) = (term86 A s x' x).
Proof. exact (@lem17646 (s x') (term49 A s x' x)). Qed.
Lemma lem3844207 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term71 A s x' x) = (term87 A s x' x).
Proof. exact (TRANS (@lem3844202 A s x' x) (@lem3844201 A s x' x)). Qed.
Lemma lem3844212 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3844274 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term71 A s x' x) : term87 A s x' x.
Proof. exact (EQ_MP (@lem3844207 A s x' x) (@lem3844160 A s x' x h1)). Qed.
Lemma lem3844275 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term83 A s x' x) : term83 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3844276 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term81 A s x' x) : term81 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3844277 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term83 A s x' x) : term79 A s x' x.
Proof. exact (proj2 (@lem3844275 A s x' x h1)). Qed.
Lemma lem3844279 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term83 A s x' x) : term75 A s x' x.
Proof. exact (proj2 (@lem3844277 A s x' x h1)). Qed.
Lemma lem3844283 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term81 A s x' x) : term49 A s x' x.
Proof. exact (proj2 (@lem3844276 A s x' x h1)). Qed.
Lemma lem3844286 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term47 A s x' x) : term47 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3844304 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term88 A s x') : term88 A s x'.
Proof. exact (h1). Qed.
Lemma lem3844320 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3844324 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3844332 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3844356 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term88 A s x') : term88 A s x'.
Proof. exact (h1). Qed.
Lemma lem3844362 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term83 A s x' x) : term46 A x' x.
Proof. exact (proj1 (@lem3844277 A s x' x h1)). Qed.
Lemma lem3844364 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3844366 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3844368 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term81 A s x' x) : term88 A s x'.
Proof. exact (proj1 (@lem3844276 A s x' x h1)). Qed.
Lemma lem3844370 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3844374 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term81 A s x' x) : term88 A s x'.
Proof. exact (proj1 (@lem3844276 A s x' x h1)). Qed.
Lemma lem3844420 {A : Type'} (x : A) : (term89 A x) = (term89 A x).
Proof. exact (eq_refl (term89 A x)). Qed.
Lemma lem3844421 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term90 A x x') = (term91 A x).
Proof. exact (MK_COMB (@lem3844420 A x) (@lem3844364 A x' x h1)). Qed.
Lemma lem3844422 {A : Type'} (x : A) : (term91 A x) = (term92 A x).
Proof. exact (eq_refl (term91 A x)). Qed.
Lemma lem3844423 {A : Type'} (x : A) (x' : A) : (term93 A x x') = (term93 A x x').
Proof. exact (eq_refl (term93 A x x')). Qed.
Lemma lem3844424 {A : Type'} (x' : A) (x : A) : ((term90 A x x') = (term91 A x)) = ((term90 A x x') = (term92 A x)).
Proof. exact (MK_COMB (@lem3844423 A x x') (@lem3844422 A x)). Qed.
Lemma lem3844425 {A : Type'} (x' : A) (x : A) : (term90 A x x') = (term46 A x' x).
Proof. exact (eq_refl (term90 A x x')). Qed.
Lemma lem3844426 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3844427 {A : Type'} (x' : A) (x : A) : (term93 A x x') = (term94 A x' x).
Proof. exact (MK_COMB (@lem3844426) (@lem3844425 A x' x)). Qed.
Lemma lem3844428 {A : Type'} (x : A) : (term92 A x) = (term92 A x).
Proof. exact (eq_refl (term92 A x)). Qed.
Lemma lem3844429 {A : Type'} (x' : A) (x : A) : ((term90 A x x') = (term92 A x)) = ((term46 A x' x) = (term92 A x)).
Proof. exact (MK_COMB (@lem3844427 A x' x) (@lem3844428 A x)). Qed.
Lemma lem3844430 {A : Type'} (x' : A) (x : A) : ((term90 A x x') = (term91 A x)) = ((term46 A x' x) = (term92 A x)).
Proof. exact (TRANS (@lem3844424 A x' x) (@lem3844429 A x' x)). Qed.
Lemma lem3844431 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term46 A x' x) = (term92 A x).
Proof. exact (EQ_MP (@lem3844430 A x' x) (@lem3844421 A x' x h1)). Qed.
Lemma lem3844432 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term83 A s x' x) (h2 : x' = x) : term92 A x.
Proof. exact (EQ_MP (@lem3844431 A x' x h2) (@lem3844362 A s x' x h1)). Qed.
Lemma lem3844460 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3844461 {A : Type'} (s : A -> Prop) : (term95 A s) = (term95 A s).
Proof. exact (eq_refl (term95 A s)). Qed.
Lemma lem3844462 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term96 A s x') = (term96 A s x).
Proof. exact (MK_COMB (@lem3844461 A s) (@lem3844370 A x' x h1)). Qed.
Lemma lem3844463 {A : Type'} (s : A -> Prop) (x : A) : (term96 A s x) = (term88 A s x).
Proof. exact (eq_refl (term96 A s x)). Qed.
Lemma lem3844464 {A : Type'} (s : A -> Prop) (x' : A) : (term97 A s x') = (term97 A s x').
Proof. exact (eq_refl (term97 A s x')). Qed.
Lemma lem3844465 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term96 A s x') = (term96 A s x)) = ((term96 A s x') = (term88 A s x)).
Proof. exact (MK_COMB (@lem3844464 A s x') (@lem3844463 A s x)). Qed.
Lemma lem3844466 {A : Type'} (s : A -> Prop) (x' : A) : (term96 A s x') = (term88 A s x').
Proof. exact (eq_refl (term96 A s x')). Qed.
Lemma lem3844467 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3844468 {A : Type'} (s : A -> Prop) (x' : A) : (term97 A s x') = (term98 A s x').
Proof. exact (MK_COMB (@lem3844467) (@lem3844466 A s x')). Qed.
Lemma lem3844469 {A : Type'} (s : A -> Prop) (x : A) : (term88 A s x) = (term88 A s x).
Proof. exact (eq_refl (term88 A s x)). Qed.
Lemma lem3844470 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term96 A s x') = (term88 A s x)) = ((term88 A s x') = (term88 A s x)).
Proof. exact (MK_COMB (@lem3844468 A s x') (@lem3844469 A s x)). Qed.
Lemma lem3844471 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term96 A s x') = (term96 A s x)) = ((term88 A s x') = (term88 A s x)).
Proof. exact (TRANS (@lem3844465 A x' s x) (@lem3844470 A x' s x)). Qed.
Lemma lem3844472 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term88 A s x') = (term88 A s x).
Proof. exact (EQ_MP (@lem3844471 A x' s x) (@lem3844462 A s x' x h1)). Qed.
Lemma lem3844473 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term81 A s x' x) (h2 : x' = x) : term88 A s x.
Proof. exact (EQ_MP (@lem3844472 A s x' x h2) (@lem3844368 A s x' x h1)). Qed.
Lemma lem3844489 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term83 A s x' x) : s x'.
Proof. exact (proj1 (@lem3844275 A s x' x h1)). Qed.
Lemma lem3844490 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term83 A s x' x) : term99 A s x'.
Proof. exact (fun h0 : term88 A s x' => @lem3844489 A s x' x h1). Qed.
Lemma lem3844492 (p : Prop) : (term100 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3844493 {A : Type'} (s : A -> Prop) (x' : A) : (term99 A s x') = (s x').
Proof. exact (@lem3844492 (s x')). Qed.
Lemma lem3844494 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term83 A s x' x) : s x'.
Proof. exact (EQ_MP (@lem3844493 A s x') (@lem3844490 A s x' x h1)). Qed.
Lemma lem3844497 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3844499 {A : Type'} (s : A -> Prop) (x' : A) : (term88 A s x') = (term101 A s x').
Proof. exact (@lem3844497 (s x')). Qed.
Lemma lem3844502 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term88 A s x') : term101 A s x'.
Proof. exact (EQ_MP (@lem3844499 A s x') (@lem3844356 A s x' h1)). Qed.
Lemma lem3844505 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term88 A s x') (h2 : term83 A s x' x) : False.
Proof. exact (@lem3844502 A s x' h1 (@lem3844494 A s x' x h2)). Qed.
Lemma lem3844506 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term88 A s x') (h2 : term83 A s x' x) : term102.
Proof. exact (fun h0 : ~ False => @lem3844505 A s x' x h1 h2). Qed.
Lemma lem3844508 (p : Prop) : (term100 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3844509 : term102 = False.
Proof. exact (@lem3844508 False). Qed.
Lemma lem3844510 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term88 A s x') (h2 : term83 A s x' x) : False.
Proof. exact (EQ_MP (@lem3844509) (@lem3844506 A s x' x h1 h2)). Qed.
Lemma lem3844526 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3844527 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3844526 A x). Qed.
Lemma lem3844528 {A : Type'} (x : A) : term103 A x.
Proof. exact (fun h0 : term92 A x => @lem3844527 A x). Qed.
Lemma lem3844530 (p : Prop) : (term100 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3844531 {A : Type'} (x : A) : (term103 A x) = (x = x).
Proof. exact (@lem3844530 (x = x)). Qed.
Lemma lem3844532 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3844531 A x) (@lem3844528 A x)). Qed.
Lemma lem3844535 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3844537 {A : Type'} (x : A) : (term92 A x) = (term104 A x).
Proof. exact (@lem3844535 (x = x)). Qed.
Lemma lem3844540 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term83 A s x' x) (h2 : x' = x) : term104 A x.
Proof. exact (EQ_MP (@lem3844537 A x) (@lem3844432 A s x' x h1 h2)). Qed.
Lemma lem3844543 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term83 A s x' x) (h2 : x' = x) : False.
Proof. exact (@lem3844540 A s x' x h1 h2 (@lem3844532 A x)). Qed.
Lemma lem3844544 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term83 A s x' x) (h2 : x' = x) : term102.
Proof. exact (fun h0 : ~ False => @lem3844543 A s x' x h1 h2). Qed.
Lemma lem3844546 (p : Prop) : (term100 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3844547 : term102 = False.
Proof. exact (@lem3844546 False). Qed.
Lemma lem3844550 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3844551 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term99 A s x.
Proof. exact (fun h0 : term88 A s x => @lem3844550 A s x h1). Qed.
Lemma lem3844553 (p : Prop) : (term100 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3844554 {A : Type'} (s : A -> Prop) (x : A) : (term99 A s x) = (s x).
Proof. exact (@lem3844553 (s x)). Qed.
Lemma lem3844555 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3844554 A s x) (@lem3844551 A s x h1)). Qed.
Lemma lem3844558 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3844560 {A : Type'} (s : A -> Prop) (x : A) : (term88 A s x) = (term101 A s x).
Proof. exact (@lem3844558 (s x)). Qed.
Lemma lem3844563 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term81 A s x' x) (h2 : x' = x) : term101 A s x.
Proof. exact (EQ_MP (@lem3844560 A s x) (@lem3844473 A s x' x h1 h2)). Qed.
Lemma lem3844566 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term81 A s x' x) (h3 : x' = x) : False.
Proof. exact (@lem3844563 A s x' x h2 h3 (@lem3844555 A s x h1)). Qed.
Lemma lem3844567 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term81 A s x' x) (h3 : x' = x) : term102.
Proof. exact (fun h0 : ~ False => @lem3844566 A s x' x h1 h2 h3). Qed.
Lemma lem3844569 (p : Prop) : (term100 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3844570 : term102 = False.
Proof. exact (@lem3844569 False). Qed.
Lemma lem3844571 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term81 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3844570) (@lem3844567 A s x' x h1 h2 h3)). Qed.
Lemma lem3844587 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term47 A s x' x) : s x'.
Proof. exact (proj1 (@lem3844286 A s x' x h1)). Qed.
Lemma lem3844588 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term47 A s x' x) : term99 A s x'.
Proof. exact (fun h0 : term88 A s x' => @lem3844587 A s x' x h1). Qed.
Lemma lem3844590 (p : Prop) : (term100 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3844591 {A : Type'} (s : A -> Prop) (x' : A) : (term99 A s x') = (s x').
Proof. exact (@lem3844590 (s x')). Qed.
Lemma lem3844592 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term47 A s x' x) : s x'.
Proof. exact (EQ_MP (@lem3844591 A s x') (@lem3844588 A s x' x h1)). Qed.
Lemma lem3844595 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3844597 {A : Type'} (s : A -> Prop) (x' : A) : (term88 A s x') = (term101 A s x').
Proof. exact (@lem3844595 (s x')). Qed.
Lemma lem3844600 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term81 A s x' x) : term101 A s x'.
Proof. exact (EQ_MP (@lem3844597 A s x') (@lem3844374 A s x' x h1)). Qed.
Lemma lem3844603 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term81 A s x' x) (h2 : term47 A s x' x) : False.
Proof. exact (@lem3844600 A s x' x h1 (@lem3844592 A s x' x h2)). Qed.
Lemma lem3844604 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term81 A s x' x) (h2 : term47 A s x' x) : term102.
Proof. exact (fun h0 : ~ False => @lem3844603 A s x' x h1 h2). Qed.
Lemma lem3844606 (p : Prop) : (term100 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3844607 : term102 = False.
Proof. exact (@lem3844606 False). Qed.
Lemma lem3844608 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term81 A s x' x) (h2 : term47 A s x' x) : False.
Proof. exact (EQ_MP (@lem3844607) (@lem3844604 A s x' x h1 h2)). Qed.
Lemma lem3844609 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term81 A s x' x) (h3 : x' = x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3844571 A s x' x h1 h2 h3) (fun h4 : False => @lem3844460 A s x h1)). Qed.
Lemma lem3844611 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term81 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3844609 A s x' x h1 h2 h3) (@lem3844460 A s x h1)). Qed.
Lemma lem3844612 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term83 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3844547) (@lem3844544 A s x' x h1 h2)). Qed.
Lemma lem3844613 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term81 A s x' x) (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3844611 A s x' x h1 h2 h3) (fun h4 : False => @lem3844370 A x' x h3)). Qed.
Lemma lem3844614 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term81 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3844613 A s x' x h1 h2 h3) (@lem3844370 A x' x h3)). Qed.
Lemma lem3844615 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term81 A s x' x) (h3 : x' = x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3844614 A s x' x h1 h2 h3) (fun h4 : False => @lem3844366 A s x h1)). Qed.
Lemma lem3844616 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term81 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3844615 A s x' x h1 h2 h3) (@lem3844366 A s x h1)). Qed.
Lemma lem3844617 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term83 A s x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3844612 A s x' x h1 h2) (fun h3 : False => @lem3844364 A x' x h2)). Qed.
Lemma lem3844618 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term83 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3844617 A s x' x h1 h2) (@lem3844364 A x' x h2)). Qed.
Lemma lem3844619 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term88 A s x') (h2 : term83 A s x' x) : (term88 A s x') = False.
Proof. exact (prop_ext (fun h3 : term88 A s x' => @lem3844510 A s x' x h1 h2) (fun h3 : False => @lem3844356 A s x' h1)). Qed.
Lemma lem3844620 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term88 A s x') (h2 : term83 A s x' x) : False.
Proof. exact (EQ_MP (@lem3844619 A s x' x h1 h2) (@lem3844356 A s x' h1)). Qed.
Lemma lem3844621 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term81 A s x' x) (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3844616 A s x' x h1 h2 h3) (fun h4 : False => @lem3844332 A x' x h3)). Qed.
Lemma lem3844622 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term81 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3844621 A s x' x h1 h2 h3) (@lem3844332 A x' x h3)). Qed.
Lemma lem3844623 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term81 A s x' x) (h3 : x' = x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3844622 A s x' x h1 h2 h3) (fun h4 : False => @lem3844324 A s x h1)). Qed.
Lemma lem3844624 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term81 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3844623 A s x' x h1 h2 h3) (@lem3844324 A s x h1)). Qed.
Lemma lem3844625 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term83 A s x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3844618 A s x' x h1 h2) (fun h3 : False => @lem3844320 A x' x h2)). Qed.
Lemma lem3844626 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term83 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3844625 A s x' x h1 h2) (@lem3844320 A x' x h2)). Qed.
Lemma lem3844627 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term88 A s x') (h2 : term83 A s x' x) : (term88 A s x') = False.
Proof. exact (prop_ext (fun h3 : term88 A s x' => @lem3844620 A s x' x h1 h2) (fun h3 : False => @lem3844304 A s x' h1)). Qed.
Lemma lem3844628 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term88 A s x') (h2 : term83 A s x' x) : False.
Proof. exact (EQ_MP (@lem3844627 A s x' x h1 h2) (@lem3844304 A s x' h1)). Qed.
Lemma lem3844629 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term81 A s x' x) (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3844624 A s x' x h1 h2 h3) (fun h4 : False => @lem3844332 A x' x h3)). Qed.
Lemma lem3844630 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term81 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3844629 A s x' x h1 h2 h3) (@lem3844332 A x' x h3)). Qed.
Lemma lem3844631 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term81 A s x' x) (h3 : x' = x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3844630 A s x' x h1 h2 h3) (fun h4 : False => @lem3844324 A s x h1)). Qed.
Lemma lem3844632 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term81 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3844631 A s x' x h1 h2 h3) (@lem3844324 A s x h1)). Qed.
Lemma lem3844633 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term83 A s x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3844626 A s x' x h1 h2) (fun h3 : False => @lem3844320 A x' x h2)). Qed.
Lemma lem3844634 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term83 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3844633 A s x' x h1 h2) (@lem3844320 A x' x h2)). Qed.
Lemma lem3844635 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term88 A s x') (h2 : term83 A s x' x) : (term88 A s x') = False.
Proof. exact (prop_ext (fun h3 : term88 A s x' => @lem3844628 A s x' x h1 h2) (fun h3 : False => @lem3844304 A s x' h1)). Qed.
Lemma lem3844636 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term88 A s x') (h2 : term83 A s x' x) : False.
Proof. exact (EQ_MP (@lem3844635 A s x' x h1 h2) (@lem3844304 A s x' h1)). Qed.
Lemma lem3844637 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term81 A s x' x) : False.
Proof. exact (or_elim (@lem3844283 A s x' x h2) (fun h0 : x' = x => @lem3844632 A s x' x h1 h2 h0) (fun h0 : term47 A s x' x => @lem3844608 A s x' x h2 h0)). Qed.
Lemma lem3844638 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term83 A s x' x) : False.
Proof. exact (or_elim (@lem3844279 A s x' x h1) (fun h0 : term88 A s x' => @lem3844636 A s x' x h0 h1) (fun h0 : x' = x => @lem3844634 A s x' x h1 h0)). Qed.
Lemma lem3844639 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term71 A s x' x) (h2 : s x) : False.
Proof. exact (or_elim (@lem3844274 A s x' x h1) (fun h0 : term83 A s x' x => @lem3844638 A s x' x h0) (fun h0 : term81 A s x' x => @lem3844637 A s x' x h2 h0)). Qed.
Lemma lem3844640 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term71 A s x' x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3844639 A x' s x h1 h2) (fun h3 : False => @lem3844212 A s x h2)). Qed.
Lemma lem3844641 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term71 A s x' x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3844640 A x' s x h1 h2) (@lem3844212 A s x h2)). Qed.
Lemma lem3844642 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term71 A s x' x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3844641 A x' s x h1 h2) (fun h3 : False => @lem3844166 A s x h2)). Qed.
Lemma lem3844643 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term71 A s x' x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3844642 A x' s x h1 h2) (@lem3844166 A s x h2)). Qed.
Lemma lem3844644 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term71 A s x' x) (h2 : s x) : (term71 A s x' x) = False.
Proof. exact (prop_ext (fun h3 : term71 A s x' x => @lem3844643 A x' s x h1 h2) (fun h3 : False => @lem3844160 A s x' x h1)). Qed.
Lemma lem3844645 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term71 A s x' x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3844644 A x' s x h1 h2) (@lem3844160 A s x' x h1)). Qed.
Lemma lem3844646 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : s x) : term70 A s x' x.
Proof. exact (fun h0 : term71 A s x' x => @lem3844645 A x' s x h0 h1). Qed.
Lemma lem3844647 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : s x) : (s x') = (term49 A s x' x).
Proof. exact (EQ_MP (@lem3844159 A s x' x) (@lem3844646 A x' s x h1)). Qed.
Lemma lem3844652 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term52 A s x.
Proof. exact (fun x' : A => @lem3844647 A x' s x h1). Qed.
Lemma lem3844653 {A : Type'} (s : A -> Prop) (x : A) : term53 A s x.
Proof. exact (fun h0 : s x => @lem3844652 A s x h0). Qed.
Lemma lem3844658 {A : Type'} (x : A) : term65 A x.
Proof. exact (fun s : A -> Prop => @lem3844653 A s x). Qed.
Lemma lem3844663 {A : Type'} : term69 A.
Proof. exact (fun x : A => @lem3844658 A x). Qed.
Lemma lem3844664 {A : Type'} : term68 A.
Proof. exact (EQ_MP (@lem3844154 A) (@lem3844663 A)). Qed.
Lemma lem3844665 {A : Type'} (x : A) : term105 A x.
Proof. exact (@lem3844664 A x). Qed.
Lemma lem3844666 {A : Type'} (x : A) : (term105 A x) = (term64 A x).
Proof. exact (eq_refl (term105 A x)). Qed.
Lemma lem3844667 {A : Type'} (x : A) : term64 A x.
Proof. exact (EQ_MP (@lem3844666 A x) (@lem3844665 A x)). Qed.
Lemma lem3844668 {A : Type'} (x : A) (s : A -> Prop) : term106 A x s.
Proof. exact (@lem3844667 A x s). Qed.
Lemma lem3844669 {A : Type'} (s : A -> Prop) (x : A) : (term106 A x s) = (term55 A s x).
Proof. exact (eq_refl (term106 A x s)). Qed.
Lemma lem3844670 {A : Type'} (s : A -> Prop) (x : A) : term55 A s x.
Proof. exact (EQ_MP (@lem3844669 A s x) (@lem3844668 A x s)). Qed.
Lemma lem3844672 {A : Type'} (s : A -> Prop) (x : A) : term55 A s x.
Proof. exact (@lem3844055 A s x (@lem3844670 A s x)). Qed.
Lemma lem3844673 {A : Type'} (s : A -> Prop) (x : A) (h1 : term56 A s x) : False.
Proof. exact (@lem3844672 A s x (@lem3844039 A s x h1)). Qed.
Lemma lem3844674 {A : Type'} (s : A -> Prop) (x : A) (h1 : term56 A s x) : (term56 A s x) = False.
Proof. exact (prop_ext (fun h2 : term56 A s x => @lem3844673 A s x h1) (fun h2 : False => @lem3844039 A s x h1)). Qed.
Lemma lem3844675 {A : Type'} (s : A -> Prop) (x : A) (h1 : term56 A s x) : False.
Proof. exact (EQ_MP (@lem3844674 A s x h1) (@lem3844039 A s x h1)). Qed.
Lemma lem3844676 {A : Type'} (s : A -> Prop) (x : A) : term55 A s x.
Proof. exact (fun h0 : term56 A s x => @lem3844675 A s x h0). Qed.
Lemma lem3844677 {A : Type'} (s : A -> Prop) (x : A) : term53 A s x.
Proof. exact (EQ_MP (@lem3844038 A s x) (@lem3844676 A s x)). Qed.
Lemma lem3844678 {A : Type'} (s : A -> Prop) (x : A) : term34 A s x.
Proof. exact (EQ_MP (@lem3844034 A s x) (@lem3844677 A s x)). Qed.
Lemma lem3844679 {A : Type'} (s : A -> Prop) (x : A) : term33 A s x.
Proof. exact (EQ_MP (@lem3843968 A s x) (@lem3844678 A s x)). Qed.
Lemma lem3844680 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : s = (term24 A s x).
Proof. exact (@lem3844679 A s x (@lem3843902 A x s h1)). Qed.
Lemma lem3844681 (n : nat) : term107 n.
Proof. exact (@lem137156 n). Qed.
Lemma lem3844682 (n : nat) : (term107 n) = ((term108 n) = n).
Proof. exact (eq_refl (term107 n)). Qed.
Lemma lem3844684 {A : Type'} (s : A -> Prop) : term109 A s.
Proof. exact (@lem3205803 A s). Qed.
Lemma lem3844685 {A : Type'} (s : A -> Prop) : (term109 A s) = (term110 A s).
Proof. exact (eq_refl (term109 A s)). Qed.
Lemma lem3844686 {A : Type'} (s : A -> Prop) : term110 A s.
Proof. exact (EQ_MP (@lem3844685 A s) (@lem3844684 A s)). Qed.
Lemma lem3844687 {A : Type'} (s : A -> Prop) (x : A) : term111 A s x.
Proof. exact (@lem3844686 A s x). Qed.
Lemma lem3844688 {A : Type'} (s : A -> Prop) (x : A) : (term111 A s x) = (term112 A s x).
Proof. exact (eq_refl (term111 A s x)). Qed.
Lemma lem3844689 {A : Type'} (s : A -> Prop) (x : A) : term112 A s x.
Proof. exact (EQ_MP (@lem3844688 A s x) (@lem3844687 A s x)). Qed.
Lemma lem3844690 {A : Type'} (s : A -> Prop) (x : A) (y : A) : term113 A s x y.
Proof. exact (@lem3844689 A s x y). Qed.
Lemma lem3844691 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term113 A s x y) = ((term42 A x s y) = (term43 A s x y)).
Proof. exact (eq_refl (term113 A s x y)). Qed.
Lemma lem3844693 {A : Type'} (s : A -> Prop) : term114 A s.
Proof. exact (@lem3610594 A s). Qed.
Lemma lem3844694 {A : Type'} (s : A -> Prop) : (term114 A s) = (term115 A s).
Proof. exact (eq_refl (term114 A s)). Qed.
Lemma lem3844695 {A : Type'} (s : A -> Prop) : term115 A s.
Proof. exact (EQ_MP (@lem3844694 A s) (@lem3844693 A s)). Qed.
Lemma lem3844696 {A : Type'} (s : A -> Prop) (x : A) : term116 A s x.
Proof. exact (@lem3844695 A s x). Qed.
Lemma lem3844697 {A : Type'} (x : A) (s : A -> Prop) : (term116 A s x) = ((term117 A s x) = (@FINITE A s)).
Proof. exact (eq_refl (term116 A s x)). Qed.
Lemma lem3844699 {A : Type'} : term118 A.
Proof. exact (proj2 (@lem3840691 A)). Qed.
Lemma lem3844700 {A : Type'} (x : A) : term119 A x.
Proof. exact (@lem3844699 A x). Qed.
Lemma lem3844701 {A : Type'} (x : A) : (term119 A x) = (term120 A x).
Proof. exact (eq_refl (term119 A x)). Qed.
Lemma lem3844702 {A : Type'} (x : A) : term120 A x.
Proof. exact (EQ_MP (@lem3844701 A x) (@lem3844700 A x)). Qed.
Lemma lem3844703 {A : Type'} (x : A) (s : A -> Prop) : term121 A x s.
Proof. exact (@lem3844702 A x s). Qed.
Lemma lem3844704 {A : Type'} (x : A) (s : A -> Prop) : (term121 A x s) = (term122 A x s).
Proof. exact (eq_refl (term121 A x s)). Qed.
Lemma lem3844705 {A : Type'} (x : A) (s : A -> Prop) : term122 A x s.
Proof. exact (EQ_MP (@lem3844704 A x s) (@lem3844703 A x s)). Qed.
Lemma lem3844706 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3844707 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term123 A x s) = (term124 A x s).
Proof. exact (@lem3844705 A x s (@lem3844706 A s h1)). Qed.
Lemma lem3844714 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem3844716 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@IN A x s) = True).
Proof. exact (@lem7 (@IN A x s)). Qed.
Lemma lem3844721 {A : Type'} (x : A) (s : A -> Prop) : term122 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem3844707 A x s h0). Qed.
Lemma lem3844722 {A : Type'} (x : A) (s : A -> Prop) : term122 A x s.
Proof. exact (@lem3844721 A x s). Qed.
Lemma lem3844723 {A : Type'} (s : A -> Prop) (x : A) : term125 A s x.
Proof. exact (@lem3844722 A x (@DELETE A s x)). Qed.
Lemma lem3844725 {A : Type'} (x : A) (s : A -> Prop) : (term117 A s x) = (@FINITE A s).
Proof. exact (EQ_MP (@lem3844697 A x s) (@lem3844696 A s x)). Qed.
Lemma lem3844726 {A : Type'} (x : A) (s : A -> Prop) : (term117 A s x) = (@FINITE A s).
Proof. exact (@lem3844725 A x s). Qed.
Lemma lem3844728 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem3844714 A s) (@lem3843883 A s h1)). Qed.
Lemma lem3844729 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term117 A s x) = True.
Proof. exact (TRANS (@lem3844726 A x s) (@lem3844728 A s h1)). Qed.
Lemma lem3844730 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : True = (term117 A s x).
Proof. exact (SYM (@lem3844729 A x s h1)). Qed.
Lemma lem3844731 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : term117 A s x.
Proof. exact (EQ_MP (@lem3844730 A x s h1) (@lem0)). Qed.
Lemma lem3844732 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term25 A s x) = (term126 A s x).
Proof. exact (@lem3844723 A s x (@lem3844731 A x s h1)). Qed.
Lemma lem3844734 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term127 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem3844735 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term128 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem3844734 _2963 g t e g' t' e'). Qed.
Lemma lem3844736 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term129 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem3844735 _2963 g t e g' t'). Qed.
Lemma lem3844737 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term130 _2963 g t e.
Proof. exact (fun g' : Prop => @lem3844736 _2963 g t e g'). Qed.
Lemma lem3844738 (g : Prop) (t : nat) (e : nat) : term131 g t e.
Proof. exact (@lem3844737 nat g t e). Qed.
Lemma lem3844739 {A : Type'} (s : A -> Prop) (x : A) : term132 A s x.
Proof. exact (@lem3844738 (term133 A s x) (term9 A s x) (term134 A s x)). Qed.
Lemma lem3844740 {A : Type'} (s : A -> Prop) (x : A) (g' : Prop) : term135 A s x g'.
Proof. exact (@lem3844739 A s x g'). Qed.
Lemma lem3844741 {A : Type'} (s : A -> Prop) (x : A) (g' : Prop) : (term135 A s x g') = (term136 A s x g').
Proof. exact (eq_refl (term135 A s x g')). Qed.
Lemma lem3844742 {A : Type'} (s : A -> Prop) (x : A) (g' : Prop) : term136 A s x g'.
Proof. exact (EQ_MP (@lem3844741 A s x g') (@lem3844740 A s x g')). Qed.
Lemma lem3844743 {A : Type'} (s : A -> Prop) (x : A) (g' : Prop) (t' : nat) : term137 A s x g' t'.
Proof. exact (@lem3844742 A s x g' t'). Qed.
Lemma lem3844744 {A : Type'} (s : A -> Prop) (x : A) (g' : Prop) (t' : nat) : (term137 A s x g' t') = (term138 A s x g' t').
Proof. exact (eq_refl (term137 A s x g' t')). Qed.
Lemma lem3844745 {A : Type'} (s : A -> Prop) (x : A) (g' : Prop) (t' : nat) : term138 A s x g' t'.
Proof. exact (EQ_MP (@lem3844744 A s x g' t') (@lem3844743 A s x g' t')). Qed.
Lemma lem3844746 {A : Type'} (s : A -> Prop) (x : A) (g' : Prop) (t' : nat) (e' : nat) : term139 A s x g' t' e'.
Proof. exact (@lem3844745 A s x g' t' e'). Qed.
Lemma lem3844747 {A : Type'} (s : A -> Prop) (x : A) (g' : Prop) (t' : nat) (e' : nat) : (term139 A s x g' t' e') = (term140 A s x g' t' e').
Proof. exact (eq_refl (term139 A s x g' t' e')). Qed.
Lemma lem3844748 {A : Type'} (s : A -> Prop) (x : A) (g' : Prop) (t' : nat) (e' : nat) : term140 A s x g' t' e'.
Proof. exact (EQ_MP (@lem3844747 A s x g' t' e') (@lem3844746 A s x g' t' e')). Qed.
Lemma lem3844750 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term42 A x s y) = (term43 A s x y).
Proof. exact (EQ_MP (@lem3844691 A s x y) (@lem3844690 A s x y)). Qed.
Lemma lem3844751 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term42 A x s y) = (term43 A s x y).
Proof. exact (@lem3844750 A s x y). Qed.
Lemma lem3844752 {A : Type'} (s : A -> Prop) (x : A) : (term133 A s x) = (term141 A s x).
Proof. exact (@lem3844751 A s x x). Qed.
Lemma lem3844756 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (@IN A x s) = True.
Proof. exact (EQ_MP (@lem3844716 A x s) (@lem3843902 A x s h1)). Qed.
Lemma lem3844757 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3844758 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term44 A x s) = (and True).
Proof. exact (MK_COMB (@lem3844757) (@lem3844756 A x s h1)). Qed.
Lemma lem3844760 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3844761 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem3844760 A x). Qed.
Lemma lem3844762 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3844763 {A : Type'} (x : A) : (term92 A x) = (~ True).
Proof. exact (MK_COMB (@lem3844762) (@lem3844761 A x)). Qed.
Lemma lem3844765 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem3844766 {A : Type'} (x : A) : (term92 A x) = False.
Proof. exact (TRANS (@lem3844763 A x) (@lem3844765)). Qed.
Lemma lem3844767 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term141 A s x) = (True /\ False).
Proof. exact (MK_COMB (@lem3844758 A x s h1) (@lem3844766 A x)). Qed.
Lemma lem3844769 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3844770 : (True /\ False) = False.
Proof. exact (@lem3844769 False). Qed.
Lemma lem3844771 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term141 A s x) = False.
Proof. exact (TRANS (@lem3844767 A x s h1) (@lem3844770)). Qed.
Lemma lem3844772 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term133 A s x) = False.
Proof. exact (TRANS (@lem3844752 A s x) (@lem3844771 A x s h1)). Qed.
Lemma lem3844773 {A : Type'} (s : A -> Prop) (x : A) (t' : nat) (e' : nat) : term142 A s x t' e'.
Proof. exact (@lem3844748 A s x False t' e'). Qed.
Lemma lem3844774 {A : Type'} (t' : nat) (e' : nat) (x : A) (s : A -> Prop) (h1 : @IN A x s) : term143 A s x t' e'.
Proof. exact (@lem3844773 A s x t' e' (@lem3844772 A x s h1)). Qed.
Lemma lem3844778 {A : Type'} (s : A -> Prop) (x : A) : (term9 A s x) = (term9 A s x).
Proof. exact (eq_refl (term9 A s x)). Qed.
Lemma lem3844779 {A : Type'} (s : A -> Prop) (x : A) : term144 A s x.
Proof. exact (fun h0 : False => @lem3844778 A s x). Qed.
Lemma lem3844780 {A : Type'} (e' : nat) (x : A) (s : A -> Prop) (h1 : @IN A x s) : term145 A s x e'.
Proof. exact (@lem3844774 A (term9 A s x) e' x s h1). Qed.
Lemma lem3844781 {A : Type'} (e' : nat) (x : A) (s : A -> Prop) (h1 : @IN A x s) : term146 A s x e'.
Proof. exact (@lem3844780 A e' x s h1 (@lem3844779 A s x)). Qed.
Lemma lem3844787 {A : Type'} (s : A -> Prop) (x : A) : (term134 A s x) = (term134 A s x).
Proof. exact (eq_refl (term134 A s x)). Qed.
Lemma lem3844788 {A : Type'} (s : A -> Prop) (x : A) : term147 A s x.
Proof. exact (fun h0 : ~ False => @lem3844787 A s x). Qed.
Lemma lem3844789 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : term148 A s x.
Proof. exact (@lem3844781 A (term134 A s x) x s h1). Qed.
Lemma lem3844790 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term126 A s x) = (term149 A s x).
Proof. exact (@lem3844789 A x s h1 (@lem3844788 A s x)). Qed.
Lemma lem3844792 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem3844793 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem3844792 nat t1 t2). Qed.
Lemma lem3844794 {A : Type'} (s : A -> Prop) (x : A) : (term149 A s x) = (term134 A s x).
Proof. exact (@lem3844793 (term9 A s x) (term134 A s x)). Qed.
Lemma lem3844795 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term126 A s x) = (term134 A s x).
Proof. exact (TRANS (@lem3844790 A x s h1) (@lem3844794 A s x)). Qed.
Lemma lem3844796 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A x s) : (term25 A s x) = (term134 A s x).
Proof. exact (TRANS (@lem3844732 A x s h1) (@lem3844795 A x s h2)). Qed.
Lemma lem3844797 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem3844798 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A x s) : (term27 A s x) = (term150 A s x).
Proof. exact (MK_COMB (@lem3844797) (@lem3844796 A x s h1 h2)). Qed.
Lemma lem3844799 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem3844800 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A x s) : (term29 A s x) = (term151 A s x).
Proof. exact (MK_COMB (@lem3844798 A x s h1 h2) (@lem3844799)). Qed.
Lemma lem3844802 (n : nat) : (term108 n) = n.
Proof. exact (EQ_MP (@lem3844682 n) (@lem3844681 n)). Qed.
Lemma lem3844803 {A : Type'} (s : A -> Prop) (x : A) : (term151 A s x) = (term9 A s x).
Proof. exact (@lem3844802 (term9 A s x)). Qed.
Lemma lem3844804 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A x s) : (term29 A s x) = (term9 A s x).
Proof. exact (TRANS (@lem3844800 A x s h1 h2) (@lem3844803 A s x)). Qed.
Lemma lem3844805 {A : Type'} (s : A -> Prop) (x : A) : (term30 A s x) = (term30 A s x).
Proof. exact (eq_refl (term30 A s x)). Qed.
Lemma lem3844806 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A x s) : ((term9 A s x) = (term29 A s x)) = ((term9 A s x) = (term9 A s x)).
Proof. exact (MK_COMB (@lem3844805 A s x) (@lem3844804 A x s h1 h2)). Qed.
Lemma lem3844808 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3844809 (x : nat) : (x = x) = True.
Proof. exact (@lem3844808 nat x). Qed.
Lemma lem3844810 {A : Type'} (s : A -> Prop) (x : A) : ((term9 A s x) = (term9 A s x)) = True.
Proof. exact (@lem3844809 (term9 A s x)). Qed.
Lemma lem3844811 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A x s) : ((term9 A s x) = (term29 A s x)) = True.
Proof. exact (TRANS (@lem3844806 A x s h1 h2) (@lem3844810 A s x)). Qed.
Lemma lem3844812 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A x s) : True = ((term9 A s x) = (term29 A s x)).
Proof. exact (SYM (@lem3844811 A x s h1 h2)). Qed.
Lemma lem3844813 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A x s) : (term9 A s x) = (term29 A s x).
Proof. exact (EQ_MP (@lem3844812 A x s h1 h2) (@lem0)). Qed.
Lemma lem3844814 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : s = (term24 A s x)) (h3 : @IN A x s) : (term9 A s x) = (term7 A s).
Proof. exact (EQ_MP (@lem3843947 A s x h2) (@lem3844813 A x s h1 h3)). Qed.
Lemma lem3844815 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A x s) : (s = (term24 A s x)) = ((term9 A s x) = (term7 A s)).
Proof. exact (prop_ext (fun h3 : s = (term24 A s x) => @lem3844814 A x s h1 h3 h2) (fun h3 : (term9 A s x) = (term7 A s) => @lem3844680 A x s h2)). Qed.
Lemma lem3844817 {A : Type'} : (@CARD A) = (@CARD A).
Proof. exact (eq_refl (@CARD A)). Qed.
Lemma lem3844823 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term31 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3844824 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term31 A s t).
Proof. exact (@lem3844823 A s t). Qed.
Lemma lem3844825 {A : Type'} (x : A) (s : A -> Prop) : ((@DELETE A s x) = s) = (term152 A x s).
Proof. exact (@lem3844824 A (@DELETE A s x) s). Qed.
Lemma lem3844834 {A : Type'} (x : A) (s : A -> Prop) : (term10 A x s) = (term10 A x s).
Proof. exact (eq_refl (term10 A x s)). Qed.
Lemma lem3844835 {A : Type'} (x : A) (s : A -> Prop) : (term153 A x s) = (term154 A x s).
Proof. exact (MK_COMB (@lem3844834 A x s) (@lem3844825 A x s)). Qed.
Lemma lem3844838 {A : Type'} (x : A) (s : A -> Prop) : (term154 A x s) = (term153 A x s).
Proof. exact (SYM (@lem3844835 A x s)). Qed.
Lemma lem3844842 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3844843 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3844842 A P x). Qed.
Lemma lem3844844 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3844843 A s x). Qed.
Lemma lem3844845 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3844846 {A : Type'} (s : A -> Prop) (x : A) : (term23 A x s) = (term88 A s x).
Proof. exact (MK_COMB (@lem3844845) (@lem3844844 A s x)). Qed.
Lemma lem3844847 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3844848 {A : Type'} (s : A -> Prop) (x : A) : (term10 A x s) = (term155 A s x).
Proof. exact (MK_COMB (@lem3844847) (@lem3844846 A s x)). Qed.
Lemma lem3844856 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term42 A x s y) = (term43 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3844857 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term42 A x s y) = (term43 A s x y).
Proof. exact (@lem3844856 A s x y). Qed.
Lemma lem3844858 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term42 A x' s x) = (term43 A s x' x).
Proof. exact (@lem3844857 A s x' x). Qed.
Lemma lem3844862 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3844863 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3844862 A P x). Qed.
Lemma lem3844864 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3844863 A s x'). Qed.
Lemma lem3844865 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3844866 {A : Type'} (s : A -> Prop) (x' : A) : (term44 A x' s) = (term45 A s x').
Proof. exact (MK_COMB (@lem3844865) (@lem3844864 A s x')). Qed.
Lemma lem3844869 {A : Type'} (x' : A) (x : A) : (term46 A x' x) = (term46 A x' x).
Proof. exact (eq_refl (term46 A x' x)). Qed.
Lemma lem3844870 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term43 A s x' x) = (term47 A s x' x).
Proof. exact (MK_COMB (@lem3844866 A s x') (@lem3844869 A x' x)). Qed.
Lemma lem3844873 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term42 A x' s x) = (term47 A s x' x).
Proof. exact (TRANS (@lem3844858 A s x' x) (@lem3844870 A s x' x)). Qed.
Lemma lem3844874 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3844875 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term156 A x' s x) = (term157 A s x' x).
Proof. exact (MK_COMB (@lem3844874) (@lem3844873 A s x' x)). Qed.
Lemma lem3844877 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3844878 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3844877 A P x). Qed.
Lemma lem3844879 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3844878 A s x'). Qed.
Lemma lem3844880 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term42 A x' s x) = (@IN A x' s)) = ((term47 A s x' x) = (s x')).
Proof. exact (MK_COMB (@lem3844875 A s x' x) (@lem3844879 A s x')). Qed.
Lemma lem3844883 {A : Type'} (x : A) (s : A -> Prop) : (term158 A x s) = (term159 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3844880 A x s x')). Qed.
Lemma lem3844884 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3844885 {A : Type'} (x : A) (s : A -> Prop) : (term152 A x s) = (term160 A x s).
Proof. exact (MK_COMB (@lem3844884 A) (@lem3844883 A x s)). Qed.
Lemma lem3844890 {A : Type'} (x : A) (s : A -> Prop) : (term154 A x s) = (term161 A x s).
Proof. exact (MK_COMB (@lem3844848 A s x) (@lem3844885 A x s)). Qed.
Lemma lem3844893 {A : Type'} (x : A) (s : A -> Prop) : (term161 A x s) = (term154 A x s).
Proof. exact (SYM (@lem3844890 A x s)). Qed.
Lemma lem3844895 (p : Prop) : p = (term54 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3844896 {A : Type'} (x : A) (s : A -> Prop) : (term161 A x s) = (term162 A x s).
Proof. exact (@lem3844895 (term161 A x s)). Qed.
Lemma lem3844897 {A : Type'} (x : A) (s : A -> Prop) : (term162 A x s) = (term161 A x s).
Proof. exact (SYM (@lem3844896 A x s)). Qed.
Lemma lem3844898 {A : Type'} (x : A) (s : A -> Prop) (h1 : term163 A x s) : term163 A x s.
Proof. exact (h1). Qed.
Lemma lem3844901 {A : Type'} (x : A) (s : A -> Prop) (h1 : term162 A x s) : term162 A x s.
Proof. exact (h1). Qed.
Lemma lem3844902 {A : Type'} (x : A) (s : A -> Prop) : term164 A x s.
Proof. exact (fun h0 : term162 A x s => @lem3844901 A x s h0). Qed.
Lemma lem3844903 {A : Type'} (x : A) (s : A -> Prop) (h1 : term164 A x s) : term164 A x s.
Proof. exact (h1). Qed.
Lemma lem3844904 {A : Type'} (x : A) (s : A -> Prop) (h1 : term162 A x s) : term162 A x s.
Proof. exact (h1). Qed.
Lemma lem3844905 {A : Type'} (x : A) (s : A -> Prop) (h1 : term162 A x s) (h2 : term164 A x s) : term162 A x s.
Proof. exact (@lem3844903 A x s h2 (@lem3844904 A x s h1)). Qed.
Lemma lem3844906 {A : Type'} (x : A) (s : A -> Prop) (h1 : term162 A x s) : term165 A x s.
Proof. exact (fun h0 : term164 A x s => @lem3844905 A x s h1 h0). Qed.
Lemma lem3844907 {A : Type'} (x : A) (s : A -> Prop) (h1 : term164 A x s) : term164 A x s.
Proof. exact (h1). Qed.
Lemma lem3844908 {A : Type'} (x : A) (s : A -> Prop) (h1 : term162 A x s) (h2 : term164 A x s) : term162 A x s.
Proof. exact (@lem3844906 A x s h1 (@lem3844907 A x s h2)). Qed.
Lemma lem3844909 {A : Type'} (x : A) (s : A -> Prop) (h1 : term164 A x s) : term164 A x s.
Proof. exact (fun h0 : term162 A x s => @lem3844908 A x s h0 h1). Qed.
Lemma lem3844910 {A : Type'} (x : A) (s : A -> Prop) : term166 A x s.
Proof. exact (fun h0 : term164 A x s => @lem3844909 A x s h0). Qed.
Lemma lem3844913 {A : Type'} (x : A) (s : A -> Prop) : term164 A x s.
Proof. exact (@lem3844910 A x s (@lem3844902 A x s)). Qed.
Lemma lem3844914 {A : Type'} (x : A) (s : A -> Prop) : term164 A x s.
Proof. exact (@lem3844913 A x s). Qed.
Lemma lem3844924 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3844925 {A : Type'} (x : A) (s : A -> Prop) : (term162 A x s) = (term167 A x s).
Proof. exact (@lem3844924 (term163 A x s)). Qed.
Lemma lem3844927 (t : Prop) : (term61 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3844928 {A : Type'} (x : A) (s : A -> Prop) : (term167 A x s) = (term161 A x s).
Proof. exact (@lem3844927 (term161 A x s)). Qed.
Lemma lem3844931 {A : Type'} (x : A) (s : A -> Prop) : (term162 A x s) = (term161 A x s).
Proof. exact (TRANS (@lem3844925 A x s) (@lem3844928 A x s)). Qed.
Lemma lem3844938 {A : Type'} (s : A -> Prop) : (term168 A s) = (term169 A s).
Proof. exact (fun_ext (fun x : A => @lem3844931 A x s)). Qed.
Lemma lem3844939 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3844940 {A : Type'} (s : A -> Prop) : (term170 A s) = (term171 A s).
Proof. exact (MK_COMB (@lem3844939 A) (@lem3844938 A s)). Qed.
Lemma lem3844945 {A : Type'} : (term172 A) = (term173 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3844940 A s)). Qed.
Lemma lem3844946 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3844955 {A : Type'} : (term174 A) = (term175 A).
Proof. exact (MK_COMB (@lem3844946 A) (@lem3844945 A)). Qed.
Lemma lem3844966 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term47 A s x' x) = (s x')) = ((term47 A s x' x) = (s x')).
Proof. exact (eq_refl ((term47 A s x' x) = (s x'))). Qed.
Lemma lem3844967 {A : Type'} (x : A) (s : A -> Prop) : (term159 A x s) = (term159 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3844966 A x s x')). Qed.
Lemma lem3844968 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3844969 {A : Type'} (x : A) (s : A -> Prop) : (term160 A x s) = (term160 A x s).
Proof. exact (MK_COMB (@lem3844968 A) (@lem3844967 A x s)). Qed.
Lemma lem3844974 {A : Type'} (s : A -> Prop) (x : A) : (term155 A s x) = (term155 A s x).
Proof. exact (eq_refl (term155 A s x)). Qed.
Lemma lem3844975 {A : Type'} (x : A) (s : A -> Prop) : (term161 A x s) = (term161 A x s).
Proof. exact (MK_COMB (@lem3844974 A s x) (@lem3844969 A x s)). Qed.
Lemma lem3844976 {A : Type'} (s : A -> Prop) : (term169 A s) = (term169 A s).
Proof. exact (fun_ext (fun x : A => @lem3844975 A x s)). Qed.
Lemma lem3844977 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3844978 {A : Type'} (s : A -> Prop) : (term171 A s) = (term171 A s).
Proof. exact (MK_COMB (@lem3844977 A) (@lem3844976 A s)). Qed.
Lemma lem3844979 {A : Type'} : (term173 A) = (term173 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3844978 A s)). Qed.
Lemma lem3844980 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3844981 {A : Type'} : (term175 A) = (term175 A).
Proof. exact (MK_COMB (@lem3844980 A) (@lem3844979 A)). Qed.
Lemma lem3845006 {A : Type'} : (term174 A) = (term175 A).
Proof. exact (TRANS (@lem3844955 A) (@lem3844981 A)). Qed.
Lemma lem3845007 {A : Type'} : (term175 A) = (term174 A).
Proof. exact (SYM (@lem3845006 A)). Qed.
Lemma lem3845010 (p : Prop) : p = (term54 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3845011 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term47 A s x' x) = (s x')) = (term176 A x s x').
Proof. exact (@lem3845010 ((term47 A s x' x) = (s x'))). Qed.
Lemma lem3845012 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term176 A x s x') = ((term47 A s x' x) = (s x')).
Proof. exact (SYM (@lem3845011 A x s x')). Qed.
Lemma lem3845013 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term177 A x s x') : term177 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3845019 {A : Type'} (s : A -> Prop) (x : A) (h1 : term88 A s x) : term88 A s x.
Proof. exact (h1). Qed.
Lemma lem3845025 {A : Type'} (x' : A) (x : A) : (term72 A x' x) = (x' = x).
Proof. exact (@lem16933 (x' = x)). Qed.
Lemma lem3845027 {A : Type'} (s : A -> Prop) (x' : A) : (term73 A s x') = (term73 A s x').
Proof. exact (eq_refl (term73 A s x')). Qed.
Lemma lem3845028 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term74 A s x' x) = (term75 A s x' x).
Proof. exact (MK_COMB (@lem3845027 A s x') (@lem3845025 A x' x)). Qed.
Lemma lem3845029 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term76 A s x' x) = (term74 A s x' x).
Proof. exact (@lem17045 (s x') (term46 A x' x)). Qed.
Lemma lem3845030 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term76 A s x' x) = (term75 A s x' x).
Proof. exact (TRANS (@lem3845029 A s x' x) (@lem3845028 A s x' x)). Qed.
Lemma lem3845035 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (s x').
Proof. exact (eq_refl (s x')). Qed.
Lemma lem3845036 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3845037 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term178 A s x' x) = (term179 A s x' x).
Proof. exact (MK_COMB (@lem3845036) (@lem3845030 A s x' x)). Qed.
Lemma lem3845038 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term180 A x s x') = (term181 A x s x').
Proof. exact (MK_COMB (@lem3845037 A s x' x) (@lem3845035 A s x')). Qed.
Lemma lem3845043 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term182 A x s x') = (term182 A x s x').
Proof. exact (eq_refl (term182 A x s x')). Qed.
Lemma lem3845044 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term183 A x s x') = (term184 A x s x').
Proof. exact (MK_COMB (@lem3845043 A x s x') (@lem3845038 A x s x')). Qed.
Lemma lem3845045 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term177 A x s x') = (term183 A x s x').
Proof. exact (@lem17646 (term47 A s x' x) (s x')). Qed.
Lemma lem3845050 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term177 A x s x') = (term184 A x s x').
Proof. exact (TRANS (@lem3845045 A x s x') (@lem3845044 A x s x')). Qed.
Lemma lem3845057 {A : Type'} (s : A -> Prop) (x : A) (h1 : term88 A s x) : term88 A s x.
Proof. exact (h1). Qed.
Lemma lem3845101 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term177 A x s x') : term184 A x s x'.
Proof. exact (EQ_MP (@lem3845050 A x s x') (@lem3845013 A x s x' h1)). Qed.
Lemma lem3845102 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term185 A x s x') : term185 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3845103 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term181 A x s x') : term181 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3845105 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term185 A x s x') : term47 A s x' x.
Proof. exact (proj1 (@lem3845102 A x s x' h1)). Qed.
Lemma lem3845109 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term181 A x s x') : term75 A s x' x.
Proof. exact (proj1 (@lem3845103 A x s x' h1)). Qed.
Lemma lem3845139 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term88 A s x') : term88 A s x'.
Proof. exact (h1). Qed.
Lemma lem3845143 {A : Type'} (s : A -> Prop) (x : A) (h1 : term88 A s x) : term88 A s x.
Proof. exact (h1). Qed.
Lemma lem3845151 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3845155 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term185 A x s x') : term88 A s x'.
Proof. exact (proj2 (@lem3845102 A x s x' h1)). Qed.
Lemma lem3845165 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term88 A s x') : term88 A s x'.
Proof. exact (h1). Qed.
Lemma lem3845167 {A : Type'} (s : A -> Prop) (x : A) (h1 : term88 A s x) : term88 A s x.
Proof. exact (h1). Qed.
Lemma lem3845169 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term181 A x s x') : s x'.
Proof. exact (proj2 (@lem3845103 A x s x' h1)). Qed.
Lemma lem3845171 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3845199 {A : Type'} (s : A -> Prop) (x : A) (h1 : term88 A s x) : term88 A s x.
Proof. exact (h1). Qed.
Lemma lem3845200 {A : Type'} (s : A -> Prop) : (term186 A s) = (term186 A s).
Proof. exact (eq_refl (term186 A s)). Qed.
Lemma lem3845201 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term187 A s x') = (term187 A s x).
Proof. exact (MK_COMB (@lem3845200 A s) (@lem3845171 A x' x h1)). Qed.
Lemma lem3845202 {A : Type'} (s : A -> Prop) (x : A) : (term187 A s x) = (s x).
Proof. exact (eq_refl (term187 A s x)). Qed.
Lemma lem3845203 {A : Type'} (s : A -> Prop) (x' : A) : (term188 A s x') = (term188 A s x').
Proof. exact (eq_refl (term188 A s x')). Qed.
Lemma lem3845204 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term187 A s x') = (term187 A s x)) = ((term187 A s x') = (s x)).
Proof. exact (MK_COMB (@lem3845203 A s x') (@lem3845202 A s x)). Qed.
Lemma lem3845205 {A : Type'} (s : A -> Prop) (x' : A) : (term187 A s x') = (s x').
Proof. exact (eq_refl (term187 A s x')). Qed.
Lemma lem3845206 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3845207 {A : Type'} (s : A -> Prop) (x' : A) : (term188 A s x') = (term37 A s x').
Proof. exact (MK_COMB (@lem3845206) (@lem3845205 A s x')). Qed.
Lemma lem3845208 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3845209 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term187 A s x') = (s x)) = ((s x') = (s x)).
Proof. exact (MK_COMB (@lem3845207 A s x') (@lem3845208 A s x)). Qed.
Lemma lem3845210 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term187 A s x') = (term187 A s x)) = ((s x') = (s x)).
Proof. exact (TRANS (@lem3845204 A x' s x) (@lem3845209 A x' s x)). Qed.
Lemma lem3845211 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (s x') = (s x).
Proof. exact (EQ_MP (@lem3845210 A x' s x) (@lem3845201 A s x' x h1)). Qed.
Lemma lem3845228 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term185 A x s x') : s x'.
Proof. exact (proj1 (@lem3845105 A x s x' h1)). Qed.
Lemma lem3845229 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term185 A x s x') : term99 A s x'.
Proof. exact (fun h0 : term88 A s x' => @lem3845228 A x s x' h1). Qed.
Lemma lem3845231 (p : Prop) : (term100 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3845232 {A : Type'} (s : A -> Prop) (x' : A) : (term99 A s x') = (s x').
Proof. exact (@lem3845231 (s x')). Qed.
Lemma lem3845233 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term185 A x s x') : s x'.
Proof. exact (EQ_MP (@lem3845232 A s x') (@lem3845229 A x s x' h1)). Qed.
Lemma lem3845236 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3845238 {A : Type'} (s : A -> Prop) (x' : A) : (term88 A s x') = (term101 A s x').
Proof. exact (@lem3845236 (s x')). Qed.
Lemma lem3845241 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term185 A x s x') : term101 A s x'.
Proof. exact (EQ_MP (@lem3845238 A s x') (@lem3845155 A x s x' h1)). Qed.
Lemma lem3845244 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term185 A x s x') : False.
Proof. exact (@lem3845241 A x s x' h1 (@lem3845233 A x s x' h1)). Qed.
Lemma lem3845245 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term185 A x s x') : term102.
Proof. exact (fun h0 : ~ False => @lem3845244 A x s x' h1). Qed.
Lemma lem3845247 (p : Prop) : (term100 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3845248 : term102 = False.
Proof. exact (@lem3845247 False). Qed.
Lemma lem3845249 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term185 A x s x') : False.
Proof. exact (EQ_MP (@lem3845248) (@lem3845245 A x s x' h1)). Qed.
Lemma lem3845251 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term181 A x s x') : s x'.
Proof. exact (proj2 (@lem3845103 A x s x' h1)). Qed.
Lemma lem3845252 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term181 A x s x') : term99 A s x'.
Proof. exact (fun h0 : term88 A s x' => @lem3845251 A x s x' h1). Qed.
Lemma lem3845254 (p : Prop) : (term100 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3845255 {A : Type'} (s : A -> Prop) (x' : A) : (term99 A s x') = (s x').
Proof. exact (@lem3845254 (s x')). Qed.
Lemma lem3845256 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term181 A x s x') : s x'.
Proof. exact (EQ_MP (@lem3845255 A s x') (@lem3845252 A x s x' h1)). Qed.
Lemma lem3845259 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3845261 {A : Type'} (s : A -> Prop) (x' : A) : (term88 A s x') = (term101 A s x').
Proof. exact (@lem3845259 (s x')). Qed.
Lemma lem3845264 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term88 A s x') : term101 A s x'.
Proof. exact (EQ_MP (@lem3845261 A s x') (@lem3845165 A s x' h1)). Qed.
Lemma lem3845267 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term88 A s x') (h2 : term181 A x s x') : False.
Proof. exact (@lem3845264 A s x' h1 (@lem3845256 A x s x' h2)). Qed.
Lemma lem3845268 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term88 A s x') (h2 : term181 A x s x') : term102.
Proof. exact (fun h0 : ~ False => @lem3845267 A x s x' h1 h2). Qed.
Lemma lem3845270 (p : Prop) : (term100 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3845271 : term102 = False.
Proof. exact (@lem3845270 False). Qed.
Lemma lem3845272 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term88 A s x') (h2 : term181 A x s x') : False.
Proof. exact (EQ_MP (@lem3845271) (@lem3845268 A x s x' h1 h2)). Qed.
Lemma lem3845274 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term181 A x s x') (h2 : x' = x) : s x.
Proof. exact (EQ_MP (@lem3845211 A s x' x h2) (@lem3845169 A x s x' h1)). Qed.
Lemma lem3845275 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term181 A x s x') (h2 : x' = x) : term99 A s x.
Proof. exact (fun h0 : term88 A s x => @lem3845274 A s x' x h1 h2). Qed.
Lemma lem3845277 (p : Prop) : (term100 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3845278 {A : Type'} (s : A -> Prop) (x : A) : (term99 A s x) = (s x).
Proof. exact (@lem3845277 (s x)). Qed.
Lemma lem3845279 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term181 A x s x') (h2 : x' = x) : s x.
Proof. exact (EQ_MP (@lem3845278 A s x) (@lem3845275 A s x' x h1 h2)). Qed.
Lemma lem3845282 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3845284 {A : Type'} (s : A -> Prop) (x : A) : (term88 A s x) = (term101 A s x).
Proof. exact (@lem3845282 (s x)). Qed.
Lemma lem3845287 {A : Type'} (s : A -> Prop) (x : A) (h1 : term88 A s x) : term101 A s x.
Proof. exact (EQ_MP (@lem3845284 A s x) (@lem3845199 A s x h1)). Qed.
Lemma lem3845290 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term88 A s x) (h2 : term181 A x s x') (h3 : x' = x) : False.
Proof. exact (@lem3845287 A s x h1 (@lem3845279 A s x' x h2 h3)). Qed.
Lemma lem3845291 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term88 A s x) (h2 : term181 A x s x') (h3 : x' = x) : term102.
Proof. exact (fun h0 : ~ False => @lem3845290 A s x' x h1 h2 h3). Qed.
Lemma lem3845293 (p : Prop) : (term100 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3845294 : term102 = False.
Proof. exact (@lem3845293 False). Qed.
Lemma lem3845295 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term88 A s x) (h2 : term181 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3845294) (@lem3845291 A s x' x h1 h2 h3)). Qed.
Lemma lem3845296 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term88 A s x) (h2 : term181 A x s x') (h3 : x' = x) : (term88 A s x) = False.
Proof. exact (prop_ext (fun h4 : term88 A s x => @lem3845295 A s x' x h1 h2 h3) (fun h4 : False => @lem3845199 A s x h1)). Qed.
Lemma lem3845298 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term88 A s x) (h2 : term181 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3845296 A s x' x h1 h2 h3) (@lem3845199 A s x h1)). Qed.
Lemma lem3845299 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term88 A s x) (h2 : term181 A x s x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3845298 A s x' x h1 h2 h3) (fun h4 : False => @lem3845171 A x' x h3)). Qed.
Lemma lem3845300 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term88 A s x) (h2 : term181 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3845299 A s x' x h1 h2 h3) (@lem3845171 A x' x h3)). Qed.
Lemma lem3845301 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term88 A s x) (h2 : term181 A x s x') (h3 : x' = x) : (term88 A s x) = False.
Proof. exact (prop_ext (fun h4 : term88 A s x => @lem3845300 A s x' x h1 h2 h3) (fun h4 : False => @lem3845167 A s x h1)). Qed.
Lemma lem3845302 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term88 A s x) (h2 : term181 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3845301 A s x' x h1 h2 h3) (@lem3845167 A s x h1)). Qed.
Lemma lem3845303 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term88 A s x') (h2 : term181 A x s x') : (term88 A s x') = False.
Proof. exact (prop_ext (fun h3 : term88 A s x' => @lem3845272 A x s x' h1 h2) (fun h3 : False => @lem3845165 A s x' h1)). Qed.
Lemma lem3845304 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term88 A s x') (h2 : term181 A x s x') : False.
Proof. exact (EQ_MP (@lem3845303 A x s x' h1 h2) (@lem3845165 A s x' h1)). Qed.
Lemma lem3845305 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term88 A s x) (h2 : term181 A x s x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3845302 A s x' x h1 h2 h3) (fun h4 : False => @lem3845151 A x' x h3)). Qed.
Lemma lem3845306 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term88 A s x) (h2 : term181 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3845305 A s x' x h1 h2 h3) (@lem3845151 A x' x h3)). Qed.
Lemma lem3845307 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term88 A s x) (h2 : term181 A x s x') (h3 : x' = x) : (term88 A s x) = False.
Proof. exact (prop_ext (fun h4 : term88 A s x => @lem3845306 A s x' x h1 h2 h3) (fun h4 : False => @lem3845143 A s x h1)). Qed.
Lemma lem3845308 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term88 A s x) (h2 : term181 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3845307 A s x' x h1 h2 h3) (@lem3845143 A s x h1)). Qed.
Lemma lem3845309 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term88 A s x') (h2 : term181 A x s x') : (term88 A s x') = False.
Proof. exact (prop_ext (fun h3 : term88 A s x' => @lem3845304 A x s x' h1 h2) (fun h3 : False => @lem3845139 A s x' h1)). Qed.
Lemma lem3845310 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term88 A s x') (h2 : term181 A x s x') : False.
Proof. exact (EQ_MP (@lem3845309 A x s x' h1 h2) (@lem3845139 A s x' h1)). Qed.
Lemma lem3845311 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term88 A s x) (h2 : term181 A x s x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3845308 A s x' x h1 h2 h3) (fun h4 : False => @lem3845151 A x' x h3)). Qed.
Lemma lem3845312 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term88 A s x) (h2 : term181 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3845311 A s x' x h1 h2 h3) (@lem3845151 A x' x h3)). Qed.
Lemma lem3845313 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term88 A s x) (h2 : term181 A x s x') (h3 : x' = x) : (term88 A s x) = False.
Proof. exact (prop_ext (fun h4 : term88 A s x => @lem3845312 A s x' x h1 h2 h3) (fun h4 : False => @lem3845143 A s x h1)). Qed.
Lemma lem3845314 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term88 A s x) (h2 : term181 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3845313 A s x' x h1 h2 h3) (@lem3845143 A s x h1)). Qed.
Lemma lem3845315 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term88 A s x') (h2 : term181 A x s x') : (term88 A s x') = False.
Proof. exact (prop_ext (fun h3 : term88 A s x' => @lem3845310 A x s x' h1 h2) (fun h3 : False => @lem3845139 A s x' h1)). Qed.
Lemma lem3845316 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term88 A s x') (h2 : term181 A x s x') : False.
Proof. exact (EQ_MP (@lem3845315 A x s x' h1 h2) (@lem3845139 A s x' h1)). Qed.
Lemma lem3845317 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term88 A s x) (h2 : term181 A x s x') : False.
Proof. exact (or_elim (@lem3845109 A x s x' h2) (fun h0 : term88 A s x' => @lem3845316 A x s x' h0 h2) (fun h0 : x' = x => @lem3845314 A s x' x h1 h2 h0)). Qed.
Lemma lem3845318 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term88 A s x) (h2 : term177 A x s x') : False.
Proof. exact (or_elim (@lem3845101 A x s x' h2) (fun h0 : term185 A x s x' => @lem3845249 A x s x' h0) (fun h0 : term181 A x s x' => @lem3845317 A x s x' h1 h0)). Qed.
Lemma lem3845319 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term88 A s x) (h2 : term177 A x s x') : (term88 A s x) = False.
Proof. exact (prop_ext (fun h3 : term88 A s x => @lem3845318 A x s x' h1 h2) (fun h3 : False => @lem3845057 A s x h1)). Qed.
Lemma lem3845320 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term88 A s x) (h2 : term177 A x s x') : False.
Proof. exact (EQ_MP (@lem3845319 A x s x' h1 h2) (@lem3845057 A s x h1)). Qed.
Lemma lem3845321 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term88 A s x) (h2 : term177 A x s x') : (term88 A s x) = False.
Proof. exact (prop_ext (fun h3 : term88 A s x => @lem3845320 A x s x' h1 h2) (fun h3 : False => @lem3845019 A s x h1)). Qed.
Lemma lem3845322 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term88 A s x) (h2 : term177 A x s x') : False.
Proof. exact (EQ_MP (@lem3845321 A x s x' h1 h2) (@lem3845019 A s x h1)). Qed.
Lemma lem3845323 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term88 A s x) (h2 : term177 A x s x') : (term177 A x s x') = False.
Proof. exact (prop_ext (fun h3 : term177 A x s x' => @lem3845322 A x s x' h1 h2) (fun h3 : False => @lem3845013 A x s x' h2)). Qed.
Lemma lem3845324 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term88 A s x) (h2 : term177 A x s x') : False.
Proof. exact (EQ_MP (@lem3845323 A x s x' h1 h2) (@lem3845013 A x s x' h2)). Qed.
Lemma lem3845325 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term88 A s x) : term176 A x s x'.
Proof. exact (fun h0 : term177 A x s x' => @lem3845324 A x s x' h1 h0). Qed.
Lemma lem3845326 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term88 A s x) : (term47 A s x' x) = (s x').
Proof. exact (EQ_MP (@lem3845012 A x s x') (@lem3845325 A x' s x h1)). Qed.
Lemma lem3845331 {A : Type'} (s : A -> Prop) (x : A) (h1 : term88 A s x) : term160 A x s.
Proof. exact (fun x' : A => @lem3845326 A x' s x h1). Qed.
Lemma lem3845332 {A : Type'} (x : A) (s : A -> Prop) : term161 A x s.
Proof. exact (fun h0 : term88 A s x => @lem3845331 A s x h0). Qed.
Lemma lem3845337 {A : Type'} (s : A -> Prop) : term171 A s.
Proof. exact (fun x : A => @lem3845332 A x s). Qed.
Lemma lem3845342 {A : Type'} : term175 A.
Proof. exact (fun s : A -> Prop => @lem3845337 A s). Qed.
Lemma lem3845343 {A : Type'} : term174 A.
Proof. exact (EQ_MP (@lem3845007 A) (@lem3845342 A)). Qed.
Lemma lem3845344 {A : Type'} (s : A -> Prop) : term189 A s.
Proof. exact (@lem3845343 A s). Qed.
Lemma lem3845345 {A : Type'} (s : A -> Prop) : (term189 A s) = (term170 A s).
Proof. exact (eq_refl (term189 A s)). Qed.
Lemma lem3845346 {A : Type'} (s : A -> Prop) : term170 A s.
Proof. exact (EQ_MP (@lem3845345 A s) (@lem3845344 A s)). Qed.
Lemma lem3845347 {A : Type'} (s : A -> Prop) (x : A) : term190 A s x.
Proof. exact (@lem3845346 A s x). Qed.
Lemma lem3845348 {A : Type'} (x : A) (s : A -> Prop) : (term190 A s x) = (term162 A x s).
Proof. exact (eq_refl (term190 A s x)). Qed.
Lemma lem3845349 {A : Type'} (x : A) (s : A -> Prop) : term162 A x s.
Proof. exact (EQ_MP (@lem3845348 A x s) (@lem3845347 A s x)). Qed.
Lemma lem3845351 {A : Type'} (x : A) (s : A -> Prop) : term162 A x s.
Proof. exact (@lem3844914 A x s (@lem3845349 A x s)). Qed.
Lemma lem3845352 {A : Type'} (x : A) (s : A -> Prop) (h1 : term163 A x s) : False.
Proof. exact (@lem3845351 A x s (@lem3844898 A x s h1)). Qed.
Lemma lem3845353 {A : Type'} (x : A) (s : A -> Prop) (h1 : term163 A x s) : (term163 A x s) = False.
Proof. exact (prop_ext (fun h2 : term163 A x s => @lem3845352 A x s h1) (fun h2 : False => @lem3844898 A x s h1)). Qed.
Lemma lem3845354 {A : Type'} (x : A) (s : A -> Prop) (h1 : term163 A x s) : False.
Proof. exact (EQ_MP (@lem3845353 A x s h1) (@lem3844898 A x s h1)). Qed.
Lemma lem3845355 {A : Type'} (x : A) (s : A -> Prop) : term162 A x s.
Proof. exact (fun h0 : term163 A x s => @lem3845354 A x s h0). Qed.
Lemma lem3845356 {A : Type'} (x : A) (s : A -> Prop) : term161 A x s.
Proof. exact (EQ_MP (@lem3844897 A x s) (@lem3845355 A x s)). Qed.
Lemma lem3845357 {A : Type'} (x : A) (s : A -> Prop) : term154 A x s.
Proof. exact (EQ_MP (@lem3844893 A x s) (@lem3845356 A x s)). Qed.
Lemma lem3845358 {A : Type'} (x : A) (s : A -> Prop) : term153 A x s.
Proof. exact (EQ_MP (@lem3844838 A x s) (@lem3845357 A x s)). Qed.
Lemma lem3845359 {A : Type'} (x : A) (s : A -> Prop) (h1 : term23 A x s) : (@DELETE A s x) = s.
Proof. exact (@lem3845358 A x s (@lem3843919 A x s h1)). Qed.
Lemma lem3845361 {A : Type'} (x : A) (s : A -> Prop) (h1 : term23 A x s) : (term9 A s x) = (@CARD A s).
Proof. exact (MK_COMB (@lem3844817 A) (@lem3845359 A x s h1)). Qed.
Lemma lem3845362 {A : Type'} (x : A) (s : A -> Prop) (h1 : term23 A x s) : (term23 A x s) = ((term9 A s x) = (@CARD A s)).
Proof. exact (prop_ext (fun h2 : term23 A x s => @lem3845361 A x s h1) (fun h2 : (term9 A s x) = (@CARD A s) => @lem3843919 A x s h1)). Qed.
Lemma lem3845363 {A : Type'} (x : A) (s : A -> Prop) (h1 : term23 A x s) : (term9 A s x) = (@CARD A s).
Proof. exact (EQ_MP (@lem3845362 A x s h1) (@lem3843919 A x s h1)). Qed.
Lemma lem3845364 {A : Type'} (x : A) (s : A -> Prop) : term12 A x s.
Proof. exact (fun h0 : term23 A x s => @lem3845363 A x s h0). Qed.
Lemma lem3845365 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A x s) : (term9 A s x) = (term7 A s).
Proof. exact (EQ_MP (@lem3844815 A x s h1 h2) (@lem3844680 A x s h2)). Qed.
Lemma lem3845366 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A x s) : (@IN A x s) = ((term9 A s x) = (term7 A s)).
Proof. exact (prop_ext (fun h3 : @IN A x s => @lem3845365 A x s h1 h2) (fun h3 : (term9 A s x) = (term7 A s) => @lem3843902 A x s h2)). Qed.
Lemma lem3845367 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A x s) : (term9 A s x) = (term7 A s).
Proof. exact (EQ_MP (@lem3845366 A x s h1 h2) (@lem3843902 A x s h2)). Qed.
Lemma lem3845368 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : term16 A x s.
Proof. exact (fun h0 : @IN A x s => @lem3845367 A x s h1 h0). Qed.
Lemma lem3845369 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : term19 A x s.
Proof. exact (conj (@lem3845368 A x s h1) (@lem3845364 A x s)). Qed.
Lemma lem3845370 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term9 A s x) = (term20 A x s).
Proof. exact (EQ_MP (@lem3843901 A x s) (@lem3845369 A x s h1)). Qed.
Lemma lem3845371 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = ((term9 A s x) = (term20 A x s)).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem3845370 A x s h1) (fun h2 : (term9 A s x) = (term20 A x s) => @lem3843883 A s h1)). Qed.
Lemma lem3845372 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term9 A s x) = (term20 A x s).
Proof. exact (EQ_MP (@lem3845371 A x s h1) (@lem3843883 A s h1)). Qed.
Lemma lem3845373 {A : Type'} (x : A) (s : A -> Prop) : term191 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem3845372 A x s h0). Qed.
Lemma lem3845378 {A : Type'} (x : A) : term192 A x.
Proof. exact (fun s : A -> Prop => @lem3845373 A x s). Qed.
Lemma lem3845383 {A : Type'} : term193 A.
Proof. exact (fun x : A => @lem3845378 A x). Qed.
