Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SIZE_BOOL_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import CARD_CLAUSES_spec.
Require Import EXTENSION_spec.
Require Import FINITE_EMPTY_spec.
Require Import FINITE_INSERT_spec.
Require Import HAS_SIZE_spec.
Require Import IN_INSERT_spec.
Require Import IN_SING_spec.
Require Import IN_UNIV_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1855_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Require Import thm513079_spec.
Require Import thm521920_spec.
Require Import thm522075_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem4593399 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem4593400 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem4593401 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem4593400 A x) (@lem4593399 A x)). Qed.
Lemma lem4593402 {A : Type'} (x : A) : term2 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem4593404 {A : Type'} (x : A) : term3 A x.
Proof. exact (@lem3205876 A x). Qed.
Lemma lem4593405 {A : Type'} (x : A) : (term3 A x) = (term4 A x).
Proof. exact (eq_refl (term3 A x)). Qed.
Lemma lem4593406 {A : Type'} (x : A) : term4 A x.
Proof. exact (EQ_MP (@lem4593405 A x) (@lem4593404 A x)). Qed.
Lemma lem4593407 {A : Type'} (x : A) (y : A) : term5 A x y.
Proof. exact (@lem4593406 A x y). Qed.
Lemma lem4593408 {A : Type'} (x : A) (y : A) : (term5 A x y) = ((term6 A x y) = (x = y)).
Proof. exact (eq_refl (term5 A x y)). Qed.
Lemma lem4593743 : term7.
Proof. exact (EQ_MP (@lem521920) (@lem522075)). Qed.
Lemma lem4593744 : term8.
Proof. exact (proj2 (@lem4593743)). Qed.
Lemma lem4593745 : term9.
Proof. exact (proj2 (@lem4593744)). Qed.
Lemma lem4593746 : term10.
Proof. exact (proj2 (@lem4593745)). Qed.
Lemma lem4593747 : term11.
Proof. exact (proj2 (@lem4593746)). Qed.
Lemma lem4593748 : term12.
Proof. exact (proj2 (@lem4593747)). Qed.
Lemma lem4593749 : term13.
Proof. exact (proj2 (@lem4593748)). Qed.
Lemma lem4593750 : term14.
Proof. exact (proj2 (@lem4593749)). Qed.
Lemma lem4593751 : term15.
Proof. exact (proj2 (@lem4593750)). Qed.
Lemma lem4593752 : term16.
Proof. exact (proj2 (@lem4593751)). Qed.
Lemma lem4593753 (m : nat) : term17 m.
Proof. exact (@lem4593752 m). Qed.
Lemma lem4593754 (m : nat) : (term17 m) = (term18 m).
Proof. exact (eq_refl (term17 m)). Qed.
Lemma lem4593755 (m : nat) : term18 m.
Proof. exact (EQ_MP (@lem4593754 m) (@lem4593753 m)). Qed.
Lemma lem4593756 (m : nat) (n : nat) : term19 m n.
Proof. exact (@lem4593755 m n). Qed.
Lemma lem4593757 (m : nat) (n : nat) : (term19 m n) = (((BIT1 m) = (BIT1 n)) = (m = n)).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem4593773 : term20.
Proof. exact (proj1 (@lem4593749)). Qed.
Lemma lem4593774 (m : nat) : term21 m.
Proof. exact (@lem4593773 m). Qed.
Lemma lem4593775 (m : nat) : (term21 m) = (term22 m).
Proof. exact (eq_refl (term21 m)). Qed.
Lemma lem4593776 (m : nat) : term22 m.
Proof. exact (EQ_MP (@lem4593775 m) (@lem4593774 m)). Qed.
Lemma lem4593777 (m : nat) (n : nat) : term23 m n.
Proof. exact (@lem4593776 m n). Qed.
Lemma lem4593778 (m : nat) (n : nat) : (term23 m n) = (((BIT0 m) = (BIT0 n)) = (m = n)).
Proof. exact (eq_refl (term23 m n)). Qed.
Lemma lem4593797 : term24.
Proof. exact (proj1 (@lem4593743)). Qed.
Lemma lem4593798 (m : nat) : term25 m.
Proof. exact (@lem4593797 m). Qed.
Lemma lem4593799 (m : nat) : (term25 m) = (term26 m).
Proof. exact (eq_refl (term25 m)). Qed.
Lemma lem4593800 (m : nat) : term26 m.
Proof. exact (EQ_MP (@lem4593799 m) (@lem4593798 m)). Qed.
Lemma lem4593801 (m : nat) (n : nat) : term27 m n.
Proof. exact (@lem4593800 m n). Qed.
Lemma lem4593802 (m : nat) (n : nat) : (term27 m n) = (((NUMERAL m) = (NUMERAL n)) = (m = n)).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem4594035 : term28.
Proof. exact (EQ_MP (@lem513079) (@lem0)). Qed.
Lemma lem4594036 : term29.
Proof. exact (proj2 (@lem4594035)). Qed.
Lemma lem4594037 : term30.
Proof. exact (proj2 (@lem4594036)). Qed.
Lemma lem4594038 : term31.
Proof. exact (proj2 (@lem4594037)). Qed.
Lemma lem4594039 (n : nat) : term32 n.
Proof. exact (@lem4594038 n). Qed.
Lemma lem4594040 (n : nat) : (term32 n) = ((term33 n) = (term34 n)).
Proof. exact (eq_refl (term32 n)). Qed.
Lemma lem4594047 : term35.
Proof. exact (proj1 (@lem4594035)). Qed.
Lemma lem4594048 (n : nat) : term36 n.
Proof. exact (@lem4594047 n). Qed.
Lemma lem4594049 (n : nat) : (term36 n) = ((term37 n) = (term38 n)).
Proof. exact (eq_refl (term36 n)). Qed.
Lemma lem4594054 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = ((@FINITE _92140 (@EMPTY _92140)) = True).
Proof. exact (@lem7 (@FINITE _92140 (@EMPTY _92140))). Qed.
Lemma lem4594056 {A : Type'} (s : A -> Prop) : term39 A s.
Proof. exact (@lem3608316 A s). Qed.
Lemma lem4594057 {A : Type'} (s : A -> Prop) : (term39 A s) = (term40 A s).
Proof. exact (eq_refl (term39 A s)). Qed.
Lemma lem4594058 {A : Type'} (s : A -> Prop) : term40 A s.
Proof. exact (EQ_MP (@lem4594057 A s) (@lem4594056 A s)). Qed.
Lemma lem4594059 {A : Type'} (s : A -> Prop) (x : A) : term41 A s x.
Proof. exact (@lem4594058 A s x). Qed.
Lemma lem4594060 {A : Type'} (x : A) (s : A -> Prop) : (term41 A s x) = ((term42 A x s) = (@FINITE A s)).
Proof. exact (eq_refl (term41 A s x)). Qed.
Lemma lem4594062 {A : Type'} : term43 A.
Proof. exact (proj2 (@lem3840691 A)). Qed.
Lemma lem4594063 {A : Type'} (x : A) : term44 A x.
Proof. exact (@lem4594062 A x). Qed.
Lemma lem4594064 {A : Type'} (x : A) : (term44 A x) = (term45 A x).
Proof. exact (eq_refl (term44 A x)). Qed.
Lemma lem4594065 {A : Type'} (x : A) : term45 A x.
Proof. exact (EQ_MP (@lem4594064 A x) (@lem4594063 A x)). Qed.
Lemma lem4594066 {A : Type'} (x : A) (s : A -> Prop) : term46 A x s.
Proof. exact (@lem4594065 A x s). Qed.
Lemma lem4594067 {A : Type'} (x : A) (s : A -> Prop) : (term46 A x s) = (term47 A x s).
Proof. exact (eq_refl (term46 A x s)). Qed.
Lemma lem4594068 {A : Type'} (x : A) (s : A -> Prop) : term47 A x s.
Proof. exact (EQ_MP (@lem4594067 A x s) (@lem4594066 A x s)). Qed.
Lemma lem4594069 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4594070 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term48 A x s) = (term49 A x s).
Proof. exact (@lem4594068 A x s (@lem4594069 A s h1)). Qed.
Lemma lem4594077 {_100044 : Type'} (s : _100044 -> Prop) : term50 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem4594078 {_100044 : Type'} (s : _100044 -> Prop) : (term50 _100044 s) = (term51 _100044 s).
Proof. exact (eq_refl (term50 _100044 s)). Qed.
Lemma lem4594079 {_100044 : Type'} (s : _100044 -> Prop) : term51 _100044 s.
Proof. exact (EQ_MP (@lem4594078 _100044 s) (@lem4594077 _100044 s)). Qed.
Lemma lem4594080 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term52 _100044 s n.
Proof. exact (@lem4594079 _100044 s n). Qed.
Lemma lem4594081 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term52 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term53 _100044 s n)).
Proof. exact (eq_refl (term52 _100044 s n)). Qed.
Lemma lem4594083 {A : Type'} (x : A) : term54 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem4594084 {A : Type'} (x : A) : (term54 A x) = (term55 A x).
Proof. exact (eq_refl (term54 A x)). Qed.
Lemma lem4594085 {A : Type'} (x : A) : term55 A x.
Proof. exact (EQ_MP (@lem4594084 A x) (@lem4594083 A x)). Qed.
Lemma lem4594086 {A : Type'} (x : A) (y : A) : term56 A x y.
Proof. exact (@lem4594085 A x y). Qed.
Lemma lem4594087 {A : Type'} (y : A) (x : A) : (term56 A x y) = (term57 A y x).
Proof. exact (eq_refl (term56 A x y)). Qed.
Lemma lem4594088 {A : Type'} (y : A) (x : A) : term57 A y x.
Proof. exact (EQ_MP (@lem4594087 A y x) (@lem4594086 A x y)). Qed.
Lemma lem4594089 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term58 A y x s.
Proof. exact (@lem4594088 A y x s). Qed.
Lemma lem4594090 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term58 A y x s) = ((term59 A x y s) = (term60 A y x s)).
Proof. exact (eq_refl (term58 A y x s)). Qed.
Lemma lem4594092 {A : Type'} (x : A) : term61 A x.
Proof. exact (@lem3204818 A x). Qed.
Lemma lem4594093 {A : Type'} (x : A) : (term61 A x) = (@IN A x (@UNIV A)).
Proof. exact (eq_refl (term61 A x)). Qed.
Lemma lem4594094 {A : Type'} (x : A) : @IN A x (@UNIV A).
Proof. exact (EQ_MP (@lem4594093 A x) (@lem4594092 A x)). Qed.
Lemma lem4594095 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = ((@IN A x (@UNIV A)) = True).
Proof. exact (@lem7 (@IN A x (@UNIV A))). Qed.
Lemma lem4594097 {A : Type'} (s : A -> Prop) : term62 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4594098 {A : Type'} (s : A -> Prop) : (term62 A s) = (term63 A s).
Proof. exact (eq_refl (term62 A s)). Qed.
Lemma lem4594099 {A : Type'} (s : A -> Prop) : term63 A s.
Proof. exact (EQ_MP (@lem4594098 A s) (@lem4594097 A s)). Qed.
Lemma lem4594100 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term64 A s t.
Proof. exact (@lem4594099 A s t). Qed.
Lemma lem4594101 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term64 A s t) = ((s = t) = (term65 A s t)).
Proof. exact (eq_refl (term64 A s t)). Qed.
Lemma lem4594103 (h1 : (@UNIV Prop) = term66) : (@UNIV Prop) = term66.
Proof. exact (h1). Qed.
Lemma lem4594104 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem4594105 (h1 : (@UNIV Prop) = term66) : term68 = term69.
Proof. exact (MK_COMB (@lem4594104) (@lem4594103 h1)). Qed.
Lemma lem4594106 : term69 = term70.
Proof. exact (eq_refl term69). Qed.
Lemma lem4594107 : term71 = term71.
Proof. exact (eq_refl term71). Qed.
Lemma lem4594108 : (term68 = term69) = (term68 = term70).
Proof. exact (MK_COMB (@lem4594107) (@lem4594106)). Qed.
Lemma lem4594109 : term68 = term72.
Proof. exact (eq_refl term68). Qed.
Lemma lem4594110 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4594111 : term71 = term73.
Proof. exact (MK_COMB (@lem4594110) (@lem4594109)). Qed.
Lemma lem4594112 : term70 = term70.
Proof. exact (eq_refl term70). Qed.
Lemma lem4594113 : (term68 = term70) = (term72 = term70).
Proof. exact (MK_COMB (@lem4594111) (@lem4594112)). Qed.
Lemma lem4594114 : (term68 = term69) = (term72 = term70).
Proof. exact (TRANS (@lem4594108) (@lem4594113)). Qed.
Lemma lem4594115 (h1 : (@UNIV Prop) = term66) : term72 = term70.
Proof. exact (EQ_MP (@lem4594114) (@lem4594105 h1)). Qed.
Lemma lem4594116 (h1 : (@UNIV Prop) = term66) : term70 = term72.
Proof. exact (SYM (@lem4594115 h1)). Qed.
Lemma lem4594120 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term65 A s t).
Proof. exact (EQ_MP (@lem4594101 A s t) (@lem4594100 A s t)). Qed.
Lemma lem4594121 (s : Prop -> Prop) (t : Prop -> Prop) : (s = t) = (term74 s t).
Proof. exact (@lem4594120 Prop s t). Qed.
Lemma lem4594122 : ((@UNIV Prop) = term66) = term75.
Proof. exact (@lem4594121 (@UNIV Prop) term66). Qed.
Lemma lem4594132 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem4594095 A x) (@lem4594094 A x)). Qed.
Lemma lem4594133 (x : Prop) : (@IN Prop x (@UNIV Prop)) = True.
Proof. exact (@lem4594132 Prop x). Qed.
Lemma lem4594134 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4594135 (x : Prop) : (term76 x) = (@eq Prop True).
Proof. exact (MK_COMB (@lem4594134) (@lem4594133 x)). Qed.
Lemma lem4594137 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term59 A x y s) = (term60 A y x s).
Proof. exact (EQ_MP (@lem4594090 A y x s) (@lem4594089 A y x s)). Qed.
Lemma lem4594138 (y : Prop) (x : Prop) (s : Prop -> Prop) : (term77 x y s) = (term78 y x s).
Proof. exact (@lem4594137 Prop y x s). Qed.
Lemma lem4594139 (x : Prop) : (term79 x) = (term80 x).
Proof. exact (@lem4594138 False x (@INSERT Prop True (@EMPTY Prop))). Qed.
Lemma lem4594143 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4594144 (x : Prop) : (x = False) = (~ x).
Proof. exact (@lem4594143 x). Qed.
Lemma lem4594145 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4594146 (x : Prop) : (term81 x) = (term82 x).
Proof. exact (MK_COMB (@lem4594145) (@lem4594144 x)). Qed.
Lemma lem4594148 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term59 A x y s) = (term60 A y x s).
Proof. exact (EQ_MP (@lem4594090 A y x s) (@lem4594089 A y x s)). Qed.
Lemma lem4594149 (y : Prop) (x : Prop) (s : Prop -> Prop) : (term77 x y s) = (term78 y x s).
Proof. exact (@lem4594148 Prop y x s). Qed.
Lemma lem4594150 (x : Prop) : (term83 x) = (term84 x).
Proof. exact (@lem4594149 True x (@EMPTY Prop)). Qed.
Lemma lem4594154 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem4594155 (x : Prop) : (x = True) = x.
Proof. exact (@lem4594154 x). Qed.
Lemma lem4594156 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4594157 (x : Prop) : (term85 x) = (or x).
Proof. exact (MK_COMB (@lem4594156) (@lem4594155 x)). Qed.
Lemma lem4594158 (x : Prop) : (@IN Prop x (@EMPTY Prop)) = (@IN Prop x (@EMPTY Prop)).
Proof. exact (eq_refl (@IN Prop x (@EMPTY Prop))). Qed.
Lemma lem4594159 (x : Prop) : (term84 x) = (term86 x).
Proof. exact (MK_COMB (@lem4594157 x) (@lem4594158 x)). Qed.
Lemma lem4594162 (x : Prop) : (term83 x) = (term86 x).
Proof. exact (TRANS (@lem4594150 x) (@lem4594159 x)). Qed.
Lemma lem4594163 (x : Prop) : (term80 x) = (term87 x).
Proof. exact (MK_COMB (@lem4594146 x) (@lem4594162 x)). Qed.
Lemma lem4594166 (x : Prop) : (term79 x) = (term87 x).
Proof. exact (TRANS (@lem4594139 x) (@lem4594163 x)). Qed.
Lemma lem4594167 (x : Prop) : ((@IN Prop x (@UNIV Prop)) = (term79 x)) = (True = (term87 x)).
Proof. exact (MK_COMB (@lem4594135 x) (@lem4594166 x)). Qed.
Lemma lem4594169 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem4594170 (x : Prop) : (True = (term87 x)) = (term87 x).
Proof. exact (@lem4594169 (term87 x)). Qed.
Lemma lem4594175 (x : Prop) : ((@IN Prop x (@UNIV Prop)) = (term79 x)) = (term87 x).
Proof. exact (TRANS (@lem4594167 x) (@lem4594170 x)). Qed.
Lemma lem4594176 : term88 = term89.
Proof. exact (fun_ext (fun x : Prop => @lem4594175 x)). Qed.
Lemma lem4594177 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem4594178 : term75 = term90.
Proof. exact (MK_COMB (@lem4594177) (@lem4594176)). Qed.
Lemma lem4594183 : ((@UNIV Prop) = term66) = term90.
Proof. exact (TRANS (@lem4594122) (@lem4594178)). Qed.
Lemma lem4594184 : term90 = ((@UNIV Prop) = term66).
Proof. exact (SYM (@lem4594183)). Qed.
Lemma lem4594191 (x : Prop) : term91 x.
Proof. exact (@lem9851 x). Qed.
Lemma lem4594192 (x : Prop) : (term91 x) = (term92 x).
Proof. exact (eq_refl (term91 x)). Qed.
Lemma lem4594193 (x : Prop) : term92 x.
Proof. exact (EQ_MP (@lem4594192 x) (@lem4594191 x)). Qed.
Lemma lem4594194 (x : Prop) (h1 : x = True) : x = True.
Proof. exact (h1). Qed.
Lemma lem4594195 (x : Prop) (h1 : x = False) : x = False.
Proof. exact (h1). Qed.
Lemma lem4594202 : term89 = term89.
Proof. exact (eq_refl term89). Qed.
Lemma lem4594203 (x : Prop) (h1 : x = True) : (term93 x) = term94.
Proof. exact (MK_COMB (@lem4594202) (@lem4594194 x h1)). Qed.
Lemma lem4594204 : term94 = term95.
Proof. exact (eq_refl term94). Qed.
Lemma lem4594205 (x : Prop) : (term96 x) = (term96 x).
Proof. exact (eq_refl (term96 x)). Qed.
Lemma lem4594206 (x : Prop) : ((term93 x) = term94) = ((term93 x) = term95).
Proof. exact (MK_COMB (@lem4594205 x) (@lem4594204)). Qed.
Lemma lem4594207 (x : Prop) : (term93 x) = (term87 x).
Proof. exact (eq_refl (term93 x)). Qed.
Lemma lem4594208 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4594209 (x : Prop) : (term96 x) = (term97 x).
Proof. exact (MK_COMB (@lem4594208) (@lem4594207 x)). Qed.
Lemma lem4594210 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem4594211 (x : Prop) : ((term93 x) = term95) = ((term87 x) = term95).
Proof. exact (MK_COMB (@lem4594209 x) (@lem4594210)). Qed.
Lemma lem4594212 (x : Prop) : ((term93 x) = term94) = ((term87 x) = term95).
Proof. exact (TRANS (@lem4594206 x) (@lem4594211 x)). Qed.
Lemma lem4594213 (x : Prop) (h1 : x = True) : (term87 x) = term95.
Proof. exact (EQ_MP (@lem4594212 x) (@lem4594203 x h1)). Qed.
Lemma lem4594214 (x : Prop) (h1 : x = True) : term95 = (term87 x).
Proof. exact (SYM (@lem4594213 x h1)). Qed.
Lemma lem4594215 : term89 = term89.
Proof. exact (eq_refl term89). Qed.
Lemma lem4594216 (x : Prop) (h1 : x = False) : (term93 x) = term98.
Proof. exact (MK_COMB (@lem4594215) (@lem4594195 x h1)). Qed.
Lemma lem4594217 : term98 = term99.
Proof. exact (eq_refl term98). Qed.
Lemma lem4594218 (x : Prop) : (term96 x) = (term96 x).
Proof. exact (eq_refl (term96 x)). Qed.
Lemma lem4594219 (x : Prop) : ((term93 x) = term98) = ((term93 x) = term99).
Proof. exact (MK_COMB (@lem4594218 x) (@lem4594217)). Qed.
Lemma lem4594220 (x : Prop) : (term93 x) = (term87 x).
Proof. exact (eq_refl (term93 x)). Qed.
Lemma lem4594221 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4594222 (x : Prop) : (term96 x) = (term97 x).
Proof. exact (MK_COMB (@lem4594221) (@lem4594220 x)). Qed.
Lemma lem4594223 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem4594224 (x : Prop) : ((term93 x) = term99) = ((term87 x) = term99).
Proof. exact (MK_COMB (@lem4594222 x) (@lem4594223)). Qed.
Lemma lem4594225 (x : Prop) : ((term93 x) = term98) = ((term87 x) = term99).
Proof. exact (TRANS (@lem4594219 x) (@lem4594224 x)). Qed.
Lemma lem4594226 (x : Prop) (h1 : x = False) : (term87 x) = term99.
Proof. exact (EQ_MP (@lem4594225 x) (@lem4594216 x h1)). Qed.
Lemma lem4594227 (x : Prop) (h1 : x = False) : term99 = (term87 x).
Proof. exact (SYM (@lem4594226 x h1)). Qed.
Lemma lem4594231 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem4594232 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4594233 : term100 = (or False).
Proof. exact (MK_COMB (@lem4594232) (@lem4594231)). Qed.
Lemma lem4594235 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem4594236 : term101 = True.
Proof. exact (@lem4594235 (@IN Prop True (@EMPTY Prop))). Qed.
Lemma lem4594237 : term95 = (False \/ True).
Proof. exact (MK_COMB (@lem4594233) (@lem4594236)). Qed.
Lemma lem4594239 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem4594240 : (False \/ True) = True.
Proof. exact (@lem4594239 True). Qed.
Lemma lem4594241 : term95 = True.
Proof. exact (TRANS (@lem4594237) (@lem4594240)). Qed.
Lemma lem4594242 : True = term95.
Proof. exact (SYM (@lem4594241)). Qed.
Lemma lem4594243 : term95.
Proof. exact (EQ_MP (@lem4594242) (@lem0)). Qed.
Lemma lem4594247 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4594248 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4594249 : term102 = (or True).
Proof. exact (MK_COMB (@lem4594248) (@lem4594247)). Qed.
Lemma lem4594251 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem4594252 : term103 = (@IN Prop False (@EMPTY Prop)).
Proof. exact (@lem4594251 (@IN Prop False (@EMPTY Prop))). Qed.
Lemma lem4594253 : term99 = term104.
Proof. exact (MK_COMB (@lem4594249) (@lem4594252)). Qed.
Lemma lem4594255 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem4594256 : term104 = True.
Proof. exact (@lem4594255 (@IN Prop False (@EMPTY Prop))). Qed.
Lemma lem4594257 : term99 = True.
Proof. exact (TRANS (@lem4594253) (@lem4594256)). Qed.
Lemma lem4594258 : True = term99.
Proof. exact (SYM (@lem4594257)). Qed.
Lemma lem4594259 : term99.
Proof. exact (EQ_MP (@lem4594258) (@lem0)). Qed.
Lemma lem4594260 (x : Prop) (h1 : x = False) : term87 x.
Proof. exact (EQ_MP (@lem4594227 x h1) (@lem4594259)). Qed.
Lemma lem4594261 (x : Prop) (h1 : x = True) : term87 x.
Proof. exact (EQ_MP (@lem4594214 x h1) (@lem4594243)). Qed.
Lemma lem4594264 (x : Prop) : term87 x.
Proof. exact (or_elim (@lem4594193 x) (fun h0 : x = True => @lem4594261 x h0) (fun h0 : x = False => @lem4594260 x h0)). Qed.
Lemma lem4594269 : term90.
Proof. exact (fun x : Prop => @lem4594264 x). Qed.
Lemma lem4594270 : (@UNIV Prop) = term66.
Proof. exact (EQ_MP (@lem4594184) (@lem4594269)). Qed.
Lemma lem4594272 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term53 _100044 s n).
Proof. exact (EQ_MP (@lem4594081 _100044 s n) (@lem4594080 _100044 s n)). Qed.
Lemma lem4594273 (s : Prop -> Prop) (n : nat) : (@HAS_SIZE Prop s n) = (term105 s n).
Proof. exact (@lem4594272 Prop s n). Qed.
Lemma lem4594274 : term70 = term106.
Proof. exact (@lem4594273 term66 term107). Qed.
Lemma lem4594278 {A : Type'} (x : A) (s : A -> Prop) : (term42 A x s) = (@FINITE A s).
Proof. exact (EQ_MP (@lem4594060 A x s) (@lem4594059 A s x)). Qed.
Lemma lem4594279 (x : Prop) (s : Prop -> Prop) : (term108 x s) = (@FINITE Prop s).
Proof. exact (@lem4594278 Prop x s). Qed.
Lemma lem4594280 : term109 = term110.
Proof. exact (@lem4594279 False (@INSERT Prop True (@EMPTY Prop))). Qed.
Lemma lem4594282 {A : Type'} (x : A) (s : A -> Prop) : (term42 A x s) = (@FINITE A s).
Proof. exact (EQ_MP (@lem4594060 A x s) (@lem4594059 A s x)). Qed.
Lemma lem4594283 (x : Prop) (s : Prop -> Prop) : (term108 x s) = (@FINITE Prop s).
Proof. exact (@lem4594282 Prop x s). Qed.
Lemma lem4594284 : term110 = (@FINITE Prop (@EMPTY Prop)).
Proof. exact (@lem4594283 True (@EMPTY Prop)). Qed.
Lemma lem4594286 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem4594054 _92140) (@lem3596285 _92140)). Qed.
Lemma lem4594287 : (@FINITE Prop (@EMPTY Prop)) = True.
Proof. exact (@lem4594286 Prop). Qed.
Lemma lem4594288 : term110 = True.
Proof. exact (TRANS (@lem4594284) (@lem4594287)). Qed.
Lemma lem4594289 : term109 = True.
Proof. exact (TRANS (@lem4594280) (@lem4594288)). Qed.
Lemma lem4594290 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4594291 : term111 = (and True).
Proof. exact (MK_COMB (@lem4594290) (@lem4594289)). Qed.
Lemma lem4594295 {A : Type'} (x : A) (s : A -> Prop) : term47 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem4594070 A x s h0). Qed.
Lemma lem4594296 (x : Prop) (s : Prop -> Prop) : term112 x s.
Proof. exact (@lem4594295 Prop x s). Qed.
Lemma lem4594297 : term113.
Proof. exact (@lem4594296 False (@INSERT Prop True (@EMPTY Prop))). Qed.
Lemma lem4594299 {A : Type'} (x : A) (s : A -> Prop) : (term42 A x s) = (@FINITE A s).
Proof. exact (EQ_MP (@lem4594060 A x s) (@lem4594059 A s x)). Qed.
Lemma lem4594300 (x : Prop) (s : Prop -> Prop) : (term108 x s) = (@FINITE Prop s).
Proof. exact (@lem4594299 Prop x s). Qed.
Lemma lem4594301 : term110 = (@FINITE Prop (@EMPTY Prop)).
Proof. exact (@lem4594300 True (@EMPTY Prop)). Qed.
Lemma lem4594303 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem4594054 _92140) (@lem3596285 _92140)). Qed.
Lemma lem4594304 : (@FINITE Prop (@EMPTY Prop)) = True.
Proof. exact (@lem4594303 Prop). Qed.
Lemma lem4594305 : term110 = True.
Proof. exact (TRANS (@lem4594301) (@lem4594304)). Qed.
Lemma lem4594306 : True = term110.
Proof. exact (SYM (@lem4594305)). Qed.
Lemma lem4594307 : term110.
Proof. exact (EQ_MP (@lem4594306) (@lem0)). Qed.
Lemma lem4594308 : term114 = term115.
Proof. exact (@lem4594297 (@lem4594307)). Qed.
Lemma lem4594310 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term116 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem4594311 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term117 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem4594310 _2963 g t e g' t' e'). Qed.
Lemma lem4594312 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term118 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem4594311 _2963 g t e g' t'). Qed.
Lemma lem4594313 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term119 _2963 g t e.
Proof. exact (fun g' : Prop => @lem4594312 _2963 g t e g'). Qed.
Lemma lem4594314 (g : Prop) (t : nat) (e : nat) : term120 g t e.
Proof. exact (@lem4594313 nat g t e). Qed.
Lemma lem4594315 : term121.
Proof. exact (@lem4594314 term122 term123 term124). Qed.
Lemma lem4594316 (g' : Prop) : term125 g'.
Proof. exact (@lem4594315 g'). Qed.
Lemma lem4594317 (g' : Prop) : (term125 g') = (term126 g').
Proof. exact (eq_refl (term125 g')). Qed.
Lemma lem4594318 (g' : Prop) : term126 g'.
Proof. exact (EQ_MP (@lem4594317 g') (@lem4594316 g')). Qed.
Lemma lem4594319 (g' : Prop) (t' : nat) : term127 g' t'.
Proof. exact (@lem4594318 g' t'). Qed.
Lemma lem4594320 (g' : Prop) (t' : nat) : (term127 g' t') = (term128 g' t').
Proof. exact (eq_refl (term127 g' t')). Qed.
Lemma lem4594321 (g' : Prop) (t' : nat) : term128 g' t'.
Proof. exact (EQ_MP (@lem4594320 g' t') (@lem4594319 g' t')). Qed.
Lemma lem4594322 (g' : Prop) (t' : nat) (e' : nat) : term129 g' t' e'.
Proof. exact (@lem4594321 g' t' e'). Qed.
Lemma lem4594323 (g' : Prop) (t' : nat) (e' : nat) : (term129 g' t' e') = (term130 g' t' e').
Proof. exact (eq_refl (term129 g' t' e')). Qed.
Lemma lem4594324 (g' : Prop) (t' : nat) (e' : nat) : term130 g' t' e'.
Proof. exact (EQ_MP (@lem4594323 g' t' e') (@lem4594322 g' t' e')). Qed.
Lemma lem4594326 {A : Type'} (x : A) (y : A) : (term6 A x y) = (x = y).
Proof. exact (EQ_MP (@lem4593408 A x y) (@lem4593407 A x y)). Qed.
Lemma lem4594327 (x : Prop) (y : Prop) : (term131 x y) = (x = y).
Proof. exact (@lem4594326 Prop x y). Qed.
Lemma lem4594328 : term122 = (False = True).
Proof. exact (@lem4594327 False True). Qed.
Lemma lem4594330 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem4594331 : (False = True) = (~ True).
Proof. exact (@lem4594330 True). Qed.
Lemma lem4594333 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem4594334 : (False = True) = False.
Proof. exact (TRANS (@lem4594331) (@lem4594333)). Qed.
Lemma lem4594335 : term122 = False.
Proof. exact (TRANS (@lem4594328) (@lem4594334)). Qed.
Lemma lem4594336 (t' : nat) (e' : nat) : term132 t' e'.
Proof. exact (@lem4594324 False t' e'). Qed.
Lemma lem4594337 (t' : nat) (e' : nat) : term133 t' e'.
Proof. exact (@lem4594336 t' e' (@lem4594335)). Qed.
Lemma lem4594338 (h1 : False) : False.
Proof. exact (h1). Qed.
Lemma lem4594339 : False = (False = True).
Proof. exact (@lem7 False). Qed.
Lemma lem4594342 {A : Type'} (x : A) (s : A -> Prop) : term47 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem4594070 A x s h0). Qed.
Lemma lem4594343 (x : Prop) (s : Prop -> Prop) : term112 x s.
Proof. exact (@lem4594342 Prop x s). Qed.
Lemma lem4594344 : term134.
Proof. exact (@lem4594343 True (@EMPTY Prop)). Qed.
Lemma lem4594346 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem4594054 _92140) (@lem3596285 _92140)). Qed.
Lemma lem4594347 : (@FINITE Prop (@EMPTY Prop)) = True.
Proof. exact (@lem4594346 Prop). Qed.
Lemma lem4594348 : True = (@FINITE Prop (@EMPTY Prop)).
Proof. exact (SYM (@lem4594347)). Qed.
Lemma lem4594349 : @FINITE Prop (@EMPTY Prop).
Proof. exact (EQ_MP (@lem4594348) (@lem0)). Qed.
Lemma lem4594350 : term123 = term135.
Proof. exact (@lem4594344 (@lem4594349)). Qed.
Lemma lem4594352 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term116 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem4594353 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term117 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem4594352 _2963 g t e g' t' e'). Qed.
Lemma lem4594354 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term118 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem4594353 _2963 g t e g' t'). Qed.
Lemma lem4594355 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term119 _2963 g t e.
Proof. exact (fun g' : Prop => @lem4594354 _2963 g t e g'). Qed.
Lemma lem4594356 (g : Prop) (t : nat) (e : nat) : term120 g t e.
Proof. exact (@lem4594355 nat g t e). Qed.
Lemma lem4594357 : term136.
Proof. exact (@lem4594356 (@IN Prop True (@EMPTY Prop)) (@CARD Prop (@EMPTY Prop)) term137). Qed.
Lemma lem4594358 (g' : Prop) : term138 g'.
Proof. exact (@lem4594357 g'). Qed.
Lemma lem4594359 (g' : Prop) : (term138 g') = (term139 g').
Proof. exact (eq_refl (term138 g')). Qed.
Lemma lem4594360 (g' : Prop) : term139 g'.
Proof. exact (EQ_MP (@lem4594359 g') (@lem4594358 g')). Qed.
Lemma lem4594361 (g' : Prop) (t' : nat) : term140 g' t'.
Proof. exact (@lem4594360 g' t'). Qed.
Lemma lem4594362 (g' : Prop) (t' : nat) : (term140 g' t') = (term141 g' t').
Proof. exact (eq_refl (term140 g' t')). Qed.
Lemma lem4594363 (g' : Prop) (t' : nat) : term141 g' t'.
Proof. exact (EQ_MP (@lem4594362 g' t') (@lem4594361 g' t')). Qed.
Lemma lem4594364 (g' : Prop) (t' : nat) (e' : nat) : term142 g' t' e'.
Proof. exact (@lem4594363 g' t' e'). Qed.
Lemma lem4594365 (g' : Prop) (t' : nat) (e' : nat) : (term142 g' t' e') = (term143 g' t' e').
Proof. exact (eq_refl (term142 g' t' e')). Qed.
Lemma lem4594366 (g' : Prop) (t' : nat) (e' : nat) : term143 g' t' e'.
Proof. exact (EQ_MP (@lem4594365 g' t' e') (@lem4594364 g' t' e')). Qed.
Lemma lem4594368 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4593402 A x (@lem4593401 A x)). Qed.
Lemma lem4594369 (x : Prop) : (@IN Prop x (@EMPTY Prop)) = False.
Proof. exact (@lem4594368 Prop x). Qed.
Lemma lem4594370 : (@IN Prop True (@EMPTY Prop)) = False.
Proof. exact (@lem4594369 True). Qed.
Lemma lem4594372 (h1 : False) : False = True.
Proof. exact (EQ_MP (@lem4594339) (@lem4594338 h1)). Qed.
Lemma lem4594373 (h1 : False) : (@IN Prop True (@EMPTY Prop)) = True.
Proof. exact (TRANS (@lem4594370) (@lem4594372 h1)). Qed.
Lemma lem4594374 (t' : nat) (e' : nat) : term144 t' e'.
Proof. exact (@lem4594366 True t' e'). Qed.
Lemma lem4594375 (t' : nat) (e' : nat) (h1 : False) : term145 t' e'.
Proof. exact (@lem4594374 t' e' (@lem4594373 h1)). Qed.
Lemma lem4594382 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem4594383 : (@CARD Prop (@EMPTY Prop)) = (NUMERAL 0).
Proof. exact (@lem4594382 Prop). Qed.
Lemma lem4594384 : term146.
Proof. exact (fun h0 : True => @lem4594383). Qed.
Lemma lem4594385 (e' : nat) (h1 : False) : term147 e'.
Proof. exact (@lem4594375 (NUMERAL 0) e' h1). Qed.
Lemma lem4594386 (e' : nat) (h1 : False) : term148 e'.
Proof. exact (@lem4594385 e' h1 (@lem4594384)). Qed.
Lemma lem4594391 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem4594392 : (@CARD Prop (@EMPTY Prop)) = (NUMERAL 0).
Proof. exact (@lem4594391 Prop). Qed.
Lemma lem4594393 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem4594394 : term137 = term149.
Proof. exact (MK_COMB (@lem4594393) (@lem4594392)). Qed.
Lemma lem4594396 (n : nat) : (term37 n) = (term38 n).
Proof. exact (EQ_MP (@lem4594049 n) (@lem4594048 n)). Qed.
Lemma lem4594397 : term149 = term150.
Proof. exact (@lem4594396 0). Qed.
Lemma lem4594399 : (S 0) = (BIT1 0).
Proof. exact (proj1 (@lem4594036)). Qed.
Lemma lem4594400 : NUMERAL = NUMERAL.
Proof. exact (eq_refl NUMERAL). Qed.
Lemma lem4594401 : term150 = term151.
Proof. exact (MK_COMB (@lem4594400) (@lem4594399)). Qed.
Lemma lem4594402 : term149 = term151.
Proof. exact (TRANS (@lem4594397) (@lem4594401)). Qed.
Lemma lem4594403 : term137 = term151.
Proof. exact (TRANS (@lem4594394) (@lem4594402)). Qed.
Lemma lem4594404 : term152.
Proof. exact (fun h0 : ~ True => @lem4594403). Qed.
Lemma lem4594405 (h1 : False) : term153.
Proof. exact (@lem4594386 term151 h1). Qed.
Lemma lem4594406 (h1 : False) : term135 = term154.
Proof. exact (@lem4594405 h1 (@lem4594404)). Qed.
Lemma lem4594408 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4594409 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem4594408 nat t2 t1). Qed.
Lemma lem4594410 : term154 = (NUMERAL 0).
Proof. exact (@lem4594409 term151 (NUMERAL 0)). Qed.
Lemma lem4594411 (h1 : False) : term135 = (NUMERAL 0).
Proof. exact (TRANS (@lem4594406 h1) (@lem4594410)). Qed.
Lemma lem4594412 (h1 : False) : term123 = (NUMERAL 0).
Proof. exact (TRANS (@lem4594350) (@lem4594411 h1)). Qed.
Lemma lem4594413 : term155.
Proof. exact (fun h0 : False => @lem4594412 h0). Qed.
Lemma lem4594414 (e' : nat) : term156 e'.
Proof. exact (@lem4594337 (NUMERAL 0) e'). Qed.
Lemma lem4594415 (e' : nat) : term157 e'.
Proof. exact (@lem4594414 e' (@lem4594413)). Qed.
Lemma lem4594422 {A : Type'} (x : A) (s : A -> Prop) : term47 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem4594070 A x s h0). Qed.
Lemma lem4594423 (x : Prop) (s : Prop -> Prop) : term112 x s.
Proof. exact (@lem4594422 Prop x s). Qed.
Lemma lem4594424 : term134.
Proof. exact (@lem4594423 True (@EMPTY Prop)). Qed.
Lemma lem4594426 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem4594054 _92140) (@lem3596285 _92140)). Qed.
Lemma lem4594427 : (@FINITE Prop (@EMPTY Prop)) = True.
Proof. exact (@lem4594426 Prop). Qed.
Lemma lem4594428 : True = (@FINITE Prop (@EMPTY Prop)).
Proof. exact (SYM (@lem4594427)). Qed.
Lemma lem4594429 : @FINITE Prop (@EMPTY Prop).
Proof. exact (EQ_MP (@lem4594428) (@lem0)). Qed.
Lemma lem4594430 : term123 = term135.
Proof. exact (@lem4594424 (@lem4594429)). Qed.
Lemma lem4594432 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term116 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem4594433 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term117 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem4594432 _2963 g t e g' t' e'). Qed.
Lemma lem4594434 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term118 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem4594433 _2963 g t e g' t'). Qed.
Lemma lem4594435 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term119 _2963 g t e.
Proof. exact (fun g' : Prop => @lem4594434 _2963 g t e g'). Qed.
Lemma lem4594436 (g : Prop) (t : nat) (e : nat) : term120 g t e.
Proof. exact (@lem4594435 nat g t e). Qed.
Lemma lem4594437 : term136.
Proof. exact (@lem4594436 (@IN Prop True (@EMPTY Prop)) (@CARD Prop (@EMPTY Prop)) term137). Qed.
Lemma lem4594438 (g' : Prop) : term138 g'.
Proof. exact (@lem4594437 g'). Qed.
Lemma lem4594439 (g' : Prop) : (term138 g') = (term139 g').
Proof. exact (eq_refl (term138 g')). Qed.
Lemma lem4594440 (g' : Prop) : term139 g'.
Proof. exact (EQ_MP (@lem4594439 g') (@lem4594438 g')). Qed.
Lemma lem4594441 (g' : Prop) (t' : nat) : term140 g' t'.
Proof. exact (@lem4594440 g' t'). Qed.
Lemma lem4594442 (g' : Prop) (t' : nat) : (term140 g' t') = (term141 g' t').
Proof. exact (eq_refl (term140 g' t')). Qed.
Lemma lem4594443 (g' : Prop) (t' : nat) : term141 g' t'.
Proof. exact (EQ_MP (@lem4594442 g' t') (@lem4594441 g' t')). Qed.
Lemma lem4594444 (g' : Prop) (t' : nat) (e' : nat) : term142 g' t' e'.
Proof. exact (@lem4594443 g' t' e'). Qed.
Lemma lem4594445 (g' : Prop) (t' : nat) (e' : nat) : (term142 g' t' e') = (term143 g' t' e').
Proof. exact (eq_refl (term142 g' t' e')). Qed.
Lemma lem4594446 (g' : Prop) (t' : nat) (e' : nat) : term143 g' t' e'.
Proof. exact (EQ_MP (@lem4594445 g' t' e') (@lem4594444 g' t' e')). Qed.
Lemma lem4594448 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4593402 A x (@lem4593401 A x)). Qed.
Lemma lem4594449 (x : Prop) : (@IN Prop x (@EMPTY Prop)) = False.
Proof. exact (@lem4594448 Prop x). Qed.
Lemma lem4594450 : (@IN Prop True (@EMPTY Prop)) = False.
Proof. exact (@lem4594449 True). Qed.
Lemma lem4594453 (t' : nat) (e' : nat) : term158 t' e'.
Proof. exact (@lem4594446 False t' e'). Qed.
Lemma lem4594454 (t' : nat) (e' : nat) : term159 t' e'.
Proof. exact (@lem4594453 t' e' (@lem4594450)). Qed.
Lemma lem4594459 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem4594460 : (@CARD Prop (@EMPTY Prop)) = (NUMERAL 0).
Proof. exact (@lem4594459 Prop). Qed.
Lemma lem4594461 : term160.
Proof. exact (fun h0 : False => @lem4594460). Qed.
Lemma lem4594462 (e' : nat) : term161 e'.
Proof. exact (@lem4594454 (NUMERAL 0) e'). Qed.
Lemma lem4594463 (e' : nat) : term162 e'.
Proof. exact (@lem4594462 e' (@lem4594461)). Qed.
Lemma lem4594470 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem4594471 : (@CARD Prop (@EMPTY Prop)) = (NUMERAL 0).
Proof. exact (@lem4594470 Prop). Qed.
Lemma lem4594472 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem4594473 : term137 = term149.
Proof. exact (MK_COMB (@lem4594472) (@lem4594471)). Qed.
Lemma lem4594475 (n : nat) : (term37 n) = (term38 n).
Proof. exact (EQ_MP (@lem4594049 n) (@lem4594048 n)). Qed.
Lemma lem4594476 : term149 = term150.
Proof. exact (@lem4594475 0). Qed.
Lemma lem4594478 : (S 0) = (BIT1 0).
Proof. exact (proj1 (@lem4594036)). Qed.
Lemma lem4594479 : NUMERAL = NUMERAL.
Proof. exact (eq_refl NUMERAL). Qed.
Lemma lem4594480 : term150 = term151.
Proof. exact (MK_COMB (@lem4594479) (@lem4594478)). Qed.
Lemma lem4594481 : term149 = term151.
Proof. exact (TRANS (@lem4594476) (@lem4594480)). Qed.
Lemma lem4594482 : term137 = term151.
Proof. exact (TRANS (@lem4594473) (@lem4594481)). Qed.
Lemma lem4594483 : term163.
Proof. exact (fun h0 : ~ False => @lem4594482). Qed.
Lemma lem4594484 : term164.
Proof. exact (@lem4594463 term151). Qed.
Lemma lem4594485 : term135 = term165.
Proof. exact (@lem4594484 (@lem4594483)). Qed.
Lemma lem4594487 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4594488 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem4594487 nat t1 t2). Qed.
Lemma lem4594489 : term165 = term151.
Proof. exact (@lem4594488 (NUMERAL 0) term151). Qed.
Lemma lem4594490 : term135 = term151.
Proof. exact (TRANS (@lem4594485) (@lem4594489)). Qed.
Lemma lem4594491 : term123 = term151.
Proof. exact (TRANS (@lem4594430) (@lem4594490)). Qed.
Lemma lem4594492 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem4594493 : term124 = term166.
Proof. exact (MK_COMB (@lem4594492) (@lem4594491)). Qed.
Lemma lem4594495 (n : nat) : (term37 n) = (term38 n).
Proof. exact (EQ_MP (@lem4594049 n) (@lem4594048 n)). Qed.
Lemma lem4594496 : term166 = term167.
Proof. exact (@lem4594495 (BIT1 0)). Qed.
Lemma lem4594498 (n : nat) : (term33 n) = (term34 n).
Proof. exact (EQ_MP (@lem4594040 n) (@lem4594039 n)). Qed.
Lemma lem4594499 : term168 = term169.
Proof. exact (@lem4594498 0). Qed.
Lemma lem4594501 : (S 0) = (BIT1 0).
Proof. exact (proj1 (@lem4594036)). Qed.
Lemma lem4594502 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem4594503 : term169 = term170.
Proof. exact (MK_COMB (@lem4594502) (@lem4594501)). Qed.
Lemma lem4594504 : term168 = term170.
Proof. exact (TRANS (@lem4594499) (@lem4594503)). Qed.
Lemma lem4594505 : NUMERAL = NUMERAL.
Proof. exact (eq_refl NUMERAL). Qed.
Lemma lem4594506 : term167 = term107.
Proof. exact (MK_COMB (@lem4594505) (@lem4594504)). Qed.
Lemma lem4594507 : term166 = term107.
Proof. exact (TRANS (@lem4594496) (@lem4594506)). Qed.
Lemma lem4594508 : term124 = term107.
Proof. exact (TRANS (@lem4594493) (@lem4594507)). Qed.
Lemma lem4594509 : term171.
Proof. exact (fun h0 : ~ False => @lem4594508). Qed.
Lemma lem4594510 : term172.
Proof. exact (@lem4594415 term107). Qed.
Lemma lem4594511 : term115 = term173.
Proof. exact (@lem4594510 (@lem4594509)). Qed.
Lemma lem4594513 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4594514 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem4594513 nat t1 t2). Qed.
Lemma lem4594515 : term173 = term107.
Proof. exact (@lem4594514 (NUMERAL 0) term107). Qed.
Lemma lem4594516 : term115 = term107.
Proof. exact (TRANS (@lem4594511) (@lem4594515)). Qed.
Lemma lem4594517 : term114 = term107.
Proof. exact (TRANS (@lem4594308) (@lem4594516)). Qed.
Lemma lem4594518 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4594519 : term174 = term175.
Proof. exact (MK_COMB (@lem4594518) (@lem4594517)). Qed.
Lemma lem4594520 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem4594521 : (term114 = term107) = (term107 = term107).
Proof. exact (MK_COMB (@lem4594519) (@lem4594520)). Qed.
Lemma lem4594523 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem4593802 m n) (@lem4593801 m n)). Qed.
Lemma lem4594524 : (term107 = term107) = (term170 = term170).
Proof. exact (@lem4594523 term170 term170). Qed.
Lemma lem4594526 (m : nat) (n : nat) : ((BIT0 m) = (BIT0 n)) = (m = n).
Proof. exact (EQ_MP (@lem4593778 m n) (@lem4593777 m n)). Qed.
Lemma lem4594527 : (term170 = term170) = ((BIT1 0) = (BIT1 0)).
Proof. exact (@lem4594526 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4594529 (m : nat) (n : nat) : ((BIT1 m) = (BIT1 n)) = (m = n).
Proof. exact (EQ_MP (@lem4593757 m n) (@lem4593756 m n)). Qed.
Lemma lem4594530 : ((BIT1 0) = (BIT1 0)) = (0 = 0).
Proof. exact (@lem4594529 0 0). Qed.
Lemma lem4594532 : (0 = 0) = True.
Proof. exact (proj1 (@lem4593744)). Qed.
Lemma lem4594533 : ((BIT1 0) = (BIT1 0)) = True.
Proof. exact (TRANS (@lem4594530) (@lem4594532)). Qed.
Lemma lem4594534 : (term170 = term170) = True.
Proof. exact (TRANS (@lem4594527) (@lem4594533)). Qed.
Lemma lem4594535 : (term107 = term107) = True.
Proof. exact (TRANS (@lem4594524) (@lem4594534)). Qed.
Lemma lem4594536 : (term114 = term107) = True.
Proof. exact (TRANS (@lem4594521) (@lem4594535)). Qed.
Lemma lem4594537 : term106 = (True /\ True).
Proof. exact (MK_COMB (@lem4594291) (@lem4594536)). Qed.
Lemma lem4594539 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4594540 : (True /\ True) = True.
Proof. exact (@lem4594539 True). Qed.
Lemma lem4594541 : term106 = True.
Proof. exact (TRANS (@lem4594537) (@lem4594540)). Qed.
Lemma lem4594542 : term70 = True.
Proof. exact (TRANS (@lem4594274) (@lem4594541)). Qed.
Lemma lem4594543 : True = term70.
Proof. exact (SYM (@lem4594542)). Qed.
Lemma lem4594544 : term70.
Proof. exact (EQ_MP (@lem4594543) (@lem0)). Qed.
Lemma lem4594545 (h1 : (@UNIV Prop) = term66) : term72.
Proof. exact (EQ_MP (@lem4594116 h1) (@lem4594544)). Qed.
Lemma lem4594546 : ((@UNIV Prop) = term66) = term72.
Proof. exact (prop_ext (fun h1 : (@UNIV Prop) = term66 => @lem4594545 h1) (fun h1 : term72 => @lem4594270)). Qed.
Lemma lem4594547 : term72.
Proof. exact (EQ_MP (@lem4594546) (@lem4594270)). Qed.
