Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1096118_term_abbrevs.
Require Import SKOLEM_THM_spec.
Require Import list_RECURSION_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem1096005 {A : Type'} (REVERSE' : type1138 A) (h1 : (REVERSE' (@nil A)) = (@nil A)) : (REVERSE' (@nil A)) = (@nil A).
Proof. exact (h1). Qed.
Lemma lem1096006 {A : Type'} (REVERSE' : type1138 A) (h1 : term0 A REVERSE') : term0 A REVERSE'.
Proof. exact (h1). Qed.
Lemma lem1096007 {A : Type'} (x : A) (REVERSE' : type1138 A) (h1 : term0 A REVERSE') : term1 A REVERSE' x.
Proof. exact (@lem1096006 A REVERSE' h1 x). Qed.
Lemma lem1096008 {A : Type'} (REVERSE' : type1138 A) (x : A) : (term1 A REVERSE' x) = (term2 A REVERSE' x).
Proof. exact (eq_refl (term1 A REVERSE' x)). Qed.
Lemma lem1096009 {A : Type'} (x : A) (REVERSE' : type1138 A) (h1 : term0 A REVERSE') : term2 A REVERSE' x.
Proof. exact (EQ_MP (@lem1096008 A REVERSE' x) (@lem1096007 A x REVERSE' h1)). Qed.
Lemma lem1096010 {A : Type'} (x : A) (l : list A) (REVERSE' : type1138 A) (h1 : term0 A REVERSE') : term3 A REVERSE' x l.
Proof. exact (@lem1096009 A x REVERSE' h1 l). Qed.
Lemma lem1096011 {A : Type'} (REVERSE' : type1138 A) (l : list A) (x : A) : (term3 A REVERSE' x l) = ((term4 A REVERSE' x l) = (term5 A REVERSE' l x)).
Proof. exact (eq_refl (term3 A REVERSE' x l)). Qed.
Lemma lem1096012 {A : Type'} (l : list A) (x : A) (REVERSE' : type1138 A) (h1 : term0 A REVERSE') : (term4 A REVERSE' x l) = (term5 A REVERSE' l x).
Proof. exact (EQ_MP (@lem1096011 A REVERSE' l x) (@lem1096010 A x l REVERSE' h1)). Qed.
Lemma lem1096013 {A : Type'} (l : list A) (REVERSE' : type1138 A) (h1 : term0 A REVERSE') : term6 A REVERSE' l.
Proof. exact (fun x : A => @lem1096012 A l x REVERSE' h1). Qed.
Lemma lem1096014 {A : Type'} (REVERSE' : type1138 A) (h1 : term0 A REVERSE') : term7 A REVERSE'.
Proof. exact (fun l : list A => @lem1096013 A l REVERSE' h1). Qed.
Lemma lem1096015 {A : Type'} (REVERSE' : type1138 A) (h1 : term8 A REVERSE') : term8 A REVERSE'.
Proof. exact (h1). Qed.
Lemma lem1096016 {A : Type'} (REVERSE' : type1138 A) (h1 : term8 A REVERSE') : term0 A REVERSE'.
Proof. exact (proj2 (@lem1096015 A REVERSE' h1)). Qed.
Lemma lem1096017 {A : Type'} (REVERSE' : type1138 A) (h1 : term8 A REVERSE') : (REVERSE' (@nil A)) = (@nil A).
Proof. exact (proj1 (@lem1096015 A REVERSE' h1)). Qed.
Lemma lem1096018 {A : Type'} (REVERSE' : type1138 A) (h1 : term8 A REVERSE') : ((REVERSE' (@nil A)) = (@nil A)) = ((REVERSE' (@nil A)) = (@nil A)).
Proof. exact (prop_ext (fun h2 : (REVERSE' (@nil A)) = (@nil A) => @lem1096005 A REVERSE' h2) (fun h2 : (REVERSE' (@nil A)) = (@nil A) => @lem1096017 A REVERSE' h1)). Qed.
Lemma lem1096019 {A : Type'} (REVERSE' : type1138 A) (h1 : term8 A REVERSE') : (REVERSE' (@nil A)) = (@nil A).
Proof. exact (EQ_MP (@lem1096018 A REVERSE' h1) (@lem1096017 A REVERSE' h1)). Qed.
Lemma lem1096020 {A : Type'} (REVERSE' : type1138 A) (h1 : term8 A REVERSE') : (term0 A REVERSE') = (term7 A REVERSE').
Proof. exact (prop_ext (fun h2 : term0 A REVERSE' => @lem1096014 A REVERSE' h2) (fun h2 : term7 A REVERSE' => @lem1096016 A REVERSE' h1)). Qed.
Lemma lem1096021 {A : Type'} (REVERSE' : type1138 A) (h1 : term8 A REVERSE') : term7 A REVERSE'.
Proof. exact (EQ_MP (@lem1096020 A REVERSE' h1) (@lem1096016 A REVERSE' h1)). Qed.
Lemma lem1096022 {A : Type'} (REVERSE' : type1138 A) (h1 : term8 A REVERSE') : term9 A REVERSE'.
Proof. exact (conj (@lem1096019 A REVERSE' h1) (@lem1096021 A REVERSE' h1)). Qed.
Lemma lem1096023 {A Z : Type'} (NIL' : Z) : term10 A Z NIL'.
Proof. exact (@lem1072128 A Z NIL'). Qed.
Lemma lem1096024 {A Z : Type'} (NIL' : Z) : (term10 A Z NIL') = (term11 A Z NIL').
Proof. exact (eq_refl (term10 A Z NIL')). Qed.
Lemma lem1096025 {A Z : Type'} (NIL' : Z) : term11 A Z NIL'.
Proof. exact (EQ_MP (@lem1096024 A Z NIL') (@lem1096023 A Z NIL')). Qed.
Lemma lem1096026 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term12 A Z NIL' CONS'.
Proof. exact (@lem1096025 A Z NIL' CONS'). Qed.
Lemma lem1096027 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : (term12 A Z NIL' CONS') = (term13 A Z NIL' CONS').
Proof. exact (eq_refl (term12 A Z NIL' CONS')). Qed.
Lemma lem1096028 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term13 A Z NIL' CONS'.
Proof. exact (EQ_MP (@lem1096027 A Z NIL' CONS') (@lem1096026 A Z NIL' CONS')). Qed.
Lemma lem1096029 {A : Type'} (NIL' : list A) (CONS' : type1391 A) : term14 A NIL' CONS'.
Proof. exact (@lem1096028 A (list A) NIL' CONS'). Qed.
Lemma lem1096030 {A : Type'} : term15 A.
Proof. exact (@lem1096029 A (@nil A) (term16 A)). Qed.
Lemma lem1096031 {A : Type'} (a0 : A) : (term17 A a0) = (term18 A a0).
Proof. exact (eq_refl (term17 A a0)). Qed.
Lemma lem1096032 {A : Type'} (a1 : list A) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem1096033 {A : Type'} (a0 : A) (a1 : list A) : (term19 A a0 a1) = (term20 A a0 a1).
Proof. exact (MK_COMB (@lem1096031 A a0) (@lem1096032 A a1)). Qed.
Lemma lem1096034 {A : Type'} (a1 : list A) (a0 : A) : (term20 A a0 a1) = (term21 A a0).
Proof. exact (eq_refl (term20 A a0 a1)). Qed.
Lemma lem1096035 {A : Type'} (a1 : list A) (a0 : A) : (term19 A a0 a1) = (term21 A a0).
Proof. exact (TRANS (@lem1096033 A a0 a1) (@lem1096034 A a1 a0)). Qed.
Lemma lem1096036 {A : Type'} (fn : type1138 A) (a1 : list A) : (fn a1) = (fn a1).
Proof. exact (eq_refl (fn a1)). Qed.
Lemma lem1096037 {A : Type'} (a0 : A) (fn : type1138 A) (a1 : list A) : (term22 A a0 fn a1) = (term23 A a0 fn a1).
Proof. exact (MK_COMB (@lem1096035 A a1 a0) (@lem1096036 A fn a1)). Qed.
Lemma lem1096038 {A : Type'} (fn : type1138 A) (a1 : list A) (a0 : A) : (term23 A a0 fn a1) = (term5 A fn a1 a0).
Proof. exact (eq_refl (term23 A a0 fn a1)). Qed.
Lemma lem1096039 {A : Type'} (fn : type1138 A) (a1 : list A) (a0 : A) : (term22 A a0 fn a1) = (term5 A fn a1 a0).
Proof. exact (TRANS (@lem1096037 A a0 fn a1) (@lem1096038 A fn a1 a0)). Qed.
Lemma lem1096040 {A : Type'} (fn : type1138 A) (a0 : A) (a1 : list A) : (term24 A fn a0 a1) = (term24 A fn a0 a1).
Proof. exact (eq_refl (term24 A fn a0 a1)). Qed.
Lemma lem1096041 {A : Type'} (fn : type1138 A) (a1 : list A) (a0 : A) : ((term4 A fn a0 a1) = (term22 A a0 fn a1)) = ((term4 A fn a0 a1) = (term5 A fn a1 a0)).
Proof. exact (MK_COMB (@lem1096040 A fn a0 a1) (@lem1096039 A fn a1 a0)). Qed.
Lemma lem1096042 {A : Type'} (fn : type1138 A) (a0 : A) : (term25 A a0 fn) = (term26 A fn a0).
Proof. exact (fun_ext (fun a1 : list A => @lem1096041 A fn a1 a0)). Qed.
Lemma lem1096043 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1096044 {A : Type'} (fn : type1138 A) (a0 : A) : (term27 A a0 fn) = (term2 A fn a0).
Proof. exact (MK_COMB (@lem1096043 A) (@lem1096042 A fn a0)). Qed.
Lemma lem1096045 {A : Type'} (fn : type1138 A) : (term28 A fn) = (term29 A fn).
Proof. exact (fun_ext (fun a0 : A => @lem1096044 A fn a0)). Qed.
Lemma lem1096046 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1096047 {A : Type'} (fn : type1138 A) : (term30 A fn) = (term0 A fn).
Proof. exact (MK_COMB (@lem1096046 A) (@lem1096045 A fn)). Qed.
Lemma lem1096048 {A : Type'} (fn : type1138 A) : (term31 A fn) = (term31 A fn).
Proof. exact (eq_refl (term31 A fn)). Qed.
Lemma lem1096049 {A : Type'} (fn : type1138 A) : (term32 A fn) = (term8 A fn).
Proof. exact (MK_COMB (@lem1096048 A fn) (@lem1096047 A fn)). Qed.
Lemma lem1096050 {A : Type'} : (term33 A) = (term34 A).
Proof. exact (fun_ext (fun fn : type1138 A => @lem1096049 A fn)). Qed.
Lemma lem1096051 {A : Type'} : (@ex ((list A) -> list A)) = (@ex ((list A) -> list A)).
Proof. exact (eq_refl (@ex ((list A) -> list A))). Qed.
Lemma lem1096052 {A : Type'} : (term15 A) = (term35 A).
Proof. exact (MK_COMB (@lem1096051 A) (@lem1096050 A)). Qed.
Lemma lem1096053 {A : Type'} : term35 A.
Proof. exact (EQ_MP (@lem1096052 A) (@lem1096030 A)). Qed.
Lemma lem1096054 {A : Type'} (REVERSE' : type1138 A) (h1 : term8 A REVERSE') : term8 A REVERSE'.
Proof. exact (h1). Qed.
Lemma lem1096055 {A : Type'} (REVERSE' : type1138 A) (h1 : term8 A REVERSE') : term0 A REVERSE'.
Proof. exact (proj2 (@lem1096054 A REVERSE' h1)). Qed.
Lemma lem1096056 {A : Type'} (REVERSE' : type1138 A) (h1 : term8 A REVERSE') : (REVERSE' (@nil A)) = (@nil A).
Proof. exact (proj1 (@lem1096054 A REVERSE' h1)). Qed.
Lemma lem1096057 {A : Type'} (REVERSE' : type1138 A) (h1 : term8 A REVERSE') : term8 A REVERSE'.
Proof. exact (conj (@lem1096056 A REVERSE' h1) (@lem1096055 A REVERSE' h1)). Qed.
Lemma lem1096058 {A : Type'} (REVERSE' : type1138 A) (h1 : term8 A REVERSE') : term35 A.
Proof. exact (ex_intro (term34 A) REVERSE' (@lem1096057 A REVERSE' h1)). Qed.
Lemma lem1096059 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (h1). Qed.
Lemma lem1096060 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (ex_elim (@lem1096059 A h1) (fun REVERSE' : type1138 A => fun h0 : term34 A REVERSE' => @lem1096058 A REVERSE' h0)). Qed.
Lemma lem1096061 {A : Type'} : (term35 A) = (term35 A).
Proof. exact (prop_ext (fun h1 : term35 A => @lem1096060 A h1) (fun h1 : term35 A => @lem1096053 A)). Qed.
Lemma lem1096062 {A : Type'} : term35 A.
Proof. exact (EQ_MP (@lem1096061 A) (@lem1096053 A)). Qed.
Lemma lem1096063 {A : Type'} (REVERSE' : type1138 A) (h1 : term8 A REVERSE') : term36 A.
Proof. exact (ex_intro (term37 A) REVERSE' (@lem1096022 A REVERSE' h1)). Qed.
Lemma lem1096064 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (h1). Qed.
Lemma lem1096065 {A : Type'} (h1 : term35 A) : term36 A.
Proof. exact (ex_elim (@lem1096064 A h1) (fun REVERSE' : type1138 A => fun h0 : term34 A REVERSE' => @lem1096063 A REVERSE' h0)). Qed.
Lemma lem1096066 {A : Type'} : (term35 A) = (term36 A).
Proof. exact (prop_ext (fun h1 : term35 A => @lem1096065 A h1) (fun h1 : term36 A => @lem1096062 A)). Qed.
Lemma lem1096067 {A : Type'} : term36 A.
Proof. exact (EQ_MP (@lem1096066 A) (@lem1096062 A)). Qed.
Lemma lem1096070 {A : Type'} (REVERSE' : type1138 A) (h1 : term9 A REVERSE') : term9 A REVERSE'.
Proof. exact (h1). Qed.
Lemma lem1096071 {A : Type'} (REVERSE' : type1138 A) (h1 : term9 A REVERSE') : term36 A.
Proof. exact (ex_intro (term37 A) REVERSE' (@lem1096070 A REVERSE' h1)). Qed.
Lemma lem1096072 {A : Type'} (h1 : term36 A) : term36 A.
Proof. exact (h1). Qed.
Lemma lem1096073 {A : Type'} (h1 : term36 A) : term36 A.
Proof. exact (ex_elim (@lem1096072 A h1) (fun REVERSE' : type1138 A => fun h0 : term37 A REVERSE' => @lem1096071 A REVERSE' h0)). Qed.
Lemma lem1096074 {A : Type'} : (term36 A) = (term36 A).
Proof. exact (prop_ext (fun h1 : term36 A => @lem1096073 A h1) (fun h1 : term36 A => @lem1096067 A)). Qed.
Lemma lem1096075 {A : Type'} : term36 A.
Proof. exact (EQ_MP (@lem1096074 A) (@lem1096067 A)). Qed.
Lemma lem1096076 {A : Type'} : term38 A.
Proof. exact (fun _17939 : type1670 => @lem1096075 A). Qed.
Lemma lem1096077 {A B : Type'} (P : type1413 A B) : term39 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1096078 {A B : Type'} (P : type1413 A B) : (term39 A B P) = ((term40 A B P) = (term41 A B P)).
Proof. exact (eq_refl (term39 A B P)). Qed.
Lemma lem1096081 {A B : Type'} (P : type1413 A B) : (term40 A B P) = (term41 A B P).
Proof. exact (EQ_MP (@lem1096078 A B P) (@lem1096077 A B P)). Qed.
Lemma lem1096082 {A : Type'} (P : type1253 A) : (term42 A P) = (term43 A P).
Proof. exact (@lem1096081 type1670 (type1138 A) P). Qed.
Lemma lem1096083 {A : Type'} : (term44 A) = (term45 A).
Proof. exact (@lem1096082 A (term46 A)). Qed.
Lemma lem1096084 {A : Type'} (_17939 : type1670) : (term47 A _17939) = (term37 A).
Proof. exact (eq_refl (term47 A _17939)). Qed.
Lemma lem1096085 {A : Type'} (REVERSE' : type1138 A) : REVERSE' = REVERSE'.
Proof. exact (eq_refl REVERSE'). Qed.
Lemma lem1096086 {A : Type'} (_17939 : type1670) (REVERSE' : type1138 A) : (term48 A _17939 REVERSE') = (term49 A REVERSE').
Proof. exact (MK_COMB (@lem1096084 A _17939) (@lem1096085 A REVERSE')). Qed.
Lemma lem1096087 {A : Type'} (REVERSE' : type1138 A) : (term49 A REVERSE') = (term9 A REVERSE').
Proof. exact (eq_refl (term49 A REVERSE')). Qed.
Lemma lem1096088 {A : Type'} (_17939 : type1670) (REVERSE' : type1138 A) : (term48 A _17939 REVERSE') = (term9 A REVERSE').
Proof. exact (TRANS (@lem1096086 A _17939 REVERSE') (@lem1096087 A REVERSE')). Qed.
Lemma lem1096089 {A : Type'} (_17939 : type1670) : (term50 A _17939) = (term37 A).
Proof. exact (fun_ext (fun REVERSE' : type1138 A => @lem1096088 A _17939 REVERSE')). Qed.
Lemma lem1096090 {A : Type'} : (@ex ((list A) -> list A)) = (@ex ((list A) -> list A)).
Proof. exact (eq_refl (@ex ((list A) -> list A))). Qed.
Lemma lem1096091 {A : Type'} (_17939 : type1670) : (term51 A _17939) = (term36 A).
Proof. exact (MK_COMB (@lem1096090 A) (@lem1096089 A _17939)). Qed.
Lemma lem1096092 {A : Type'} : (term52 A) = (term53 A).
Proof. exact (fun_ext (fun _17939 : type1670 => @lem1096091 A _17939)). Qed.
Lemma lem1096093 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))). Qed.
Lemma lem1096094 {A : Type'} : (term44 A) = (term38 A).
Proof. exact (MK_COMB (@lem1096093) (@lem1096092 A)). Qed.
Lemma lem1096095 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1096096 {A : Type'} : (term54 A) = (term55 A).
Proof. exact (MK_COMB (@lem1096095) (@lem1096094 A)). Qed.
Lemma lem1096097 {A : Type'} (_17939 : type1670) : (term47 A _17939) = (term37 A).
Proof. exact (eq_refl (term47 A _17939)). Qed.
Lemma lem1096098 {A : Type'} (REVERSE' : type1258 A) (_17939 : type1670) : (REVERSE' _17939) = (REVERSE' _17939).
Proof. exact (eq_refl (REVERSE' _17939)). Qed.
Lemma lem1096099 {A : Type'} (REVERSE' : type1258 A) (_17939 : type1670) : (term56 A REVERSE' _17939) = (term57 A REVERSE' _17939).
Proof. exact (MK_COMB (@lem1096097 A _17939) (@lem1096098 A REVERSE' _17939)). Qed.
Lemma lem1096100 {A : Type'} (REVERSE' : type1258 A) (_17939 : type1670) : (term57 A REVERSE' _17939) = (term58 A REVERSE' _17939).
Proof. exact (eq_refl (term57 A REVERSE' _17939)). Qed.
Lemma lem1096101 {A : Type'} (REVERSE' : type1258 A) (_17939 : type1670) : (term56 A REVERSE' _17939) = (term58 A REVERSE' _17939).
Proof. exact (TRANS (@lem1096099 A REVERSE' _17939) (@lem1096100 A REVERSE' _17939)). Qed.
Lemma lem1096102 {A : Type'} (REVERSE' : type1258 A) : (term59 A REVERSE') = (term60 A REVERSE').
Proof. exact (fun_ext (fun _17939 : type1670 => @lem1096101 A REVERSE' _17939)). Qed.
Lemma lem1096103 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))). Qed.
Lemma lem1096104 {A : Type'} (REVERSE' : type1258 A) : (term61 A REVERSE') = (term62 A REVERSE').
Proof. exact (MK_COMB (@lem1096103) (@lem1096102 A REVERSE')). Qed.
Lemma lem1096105 {A : Type'} : (term63 A) = (term64 A).
Proof. exact (fun_ext (fun REVERSE' : type1258 A => @lem1096104 A REVERSE')). Qed.
Lemma lem1096106 {A : Type'} : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (list A) -> list A)) = (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (list A) -> list A)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (list A) -> list A))). Qed.
Lemma lem1096107 {A : Type'} : (term45 A) = (term65 A).
Proof. exact (MK_COMB (@lem1096106 A) (@lem1096105 A)). Qed.
Lemma lem1096108 {A : Type'} : ((term44 A) = (term45 A)) = ((term38 A) = (term65 A)).
Proof. exact (MK_COMB (@lem1096096 A) (@lem1096107 A)). Qed.
Lemma lem1096109 {A : Type'} : (term38 A) = (term65 A).
Proof. exact (EQ_MP (@lem1096108 A) (@lem1096083 A)). Qed.
Lemma lem1096110 {A : Type'} : term65 A.
Proof. exact (EQ_MP (@lem1096109 A) (@lem1096076 A)). Qed.
Lemma lem1096112 {A : Type'} : (@ex A) = (term66 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem1096113 {A : Type'} : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (list A) -> list A)) = (term67 A).
Proof. exact (@lem1096112 (type1258 A)). Qed.
Lemma lem1096114 {A : Type'} : (term64 A) = (term64 A).
Proof. exact (eq_refl (term64 A)). Qed.
Lemma lem1096115 {A : Type'} : (term65 A) = (term68 A).
Proof. exact (MK_COMB (@lem1096113 A) (@lem1096114 A)). Qed.
Lemma lem1096116 {A : Type'} : (term68 A) = (term69 A).
Proof. exact (eq_refl (term68 A)). Qed.
Lemma lem1096117 {A : Type'} : (term65 A) = (term69 A).
Proof. exact (TRANS (@lem1096115 A) (@lem1096116 A)). Qed.
Lemma lem1096118 {A : Type'} : term69 A.
Proof. exact (EQ_MP (@lem1096117 A) (@lem1096110 A)). Qed.
