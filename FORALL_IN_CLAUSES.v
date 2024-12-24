Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_IN_CLAUSES_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import IN_INSERT_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1822_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1856_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm82_spec.
Lemma lem5029872 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem5029873 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem5029874 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem5029873 A x) (@lem5029872 A x)). Qed.
Lemma lem5029875 {A : Type'} (x : A) : term2 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem5029877 {A : Type'} (x : A) : term3 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem5029878 {A : Type'} (x : A) : (term3 A x) = (term4 A x).
Proof. exact (eq_refl (term3 A x)). Qed.
Lemma lem5029879 {A : Type'} (x : A) : term4 A x.
Proof. exact (EQ_MP (@lem5029878 A x) (@lem5029877 A x)). Qed.
Lemma lem5029880 {A : Type'} (x : A) (y : A) : term5 A x y.
Proof. exact (@lem5029879 A x y). Qed.
Lemma lem5029881 {A : Type'} (y : A) (x : A) : (term5 A x y) = (term6 A y x).
Proof. exact (eq_refl (term5 A x y)). Qed.
Lemma lem5029882 {A : Type'} (y : A) (x : A) : term6 A y x.
Proof. exact (EQ_MP (@lem5029881 A y x) (@lem5029880 A x y)). Qed.
Lemma lem5029883 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term7 A y x s.
Proof. exact (@lem5029882 A y x s). Qed.
Lemma lem5029884 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term7 A y x s) = ((term8 A x y s) = (term9 A y x s)).
Proof. exact (eq_refl (term7 A y x s)). Qed.
Lemma lem5029893 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem5029894 {_113480 : Type'} (P : _113480 -> Prop) : ((term10 _113480 P) = True) = (term10 _113480 P).
Proof. exact (@lem5029893 (term10 _113480 P)). Qed.
Lemma lem5029902 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5029875 A x (@lem5029874 A x)). Qed.
Lemma lem5029903 {_113480 : Type'} (x : _113480) : (@IN _113480 x (@EMPTY _113480)) = False.
Proof. exact (@lem5029902 _113480 x). Qed.
Lemma lem5029904 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5029905 {_113480 : Type'} (x : _113480) : (term11 _113480 x) = (imp False).
Proof. exact (MK_COMB (@lem5029904) (@lem5029903 _113480 x)). Qed.
Lemma lem5029906 {_113480 : Type'} (P : _113480 -> Prop) (x : _113480) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem5029907 {_113480 : Type'} (P : _113480 -> Prop) (x : _113480) : (term12 _113480 P x) = (term13 _113480 P x).
Proof. exact (MK_COMB (@lem5029905 _113480 x) (@lem5029906 _113480 P x)). Qed.
Lemma lem5029909 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem5029910 {_113480 : Type'} (P : _113480 -> Prop) (x : _113480) : (term13 _113480 P x) = True.
Proof. exact (@lem5029909 (P x)). Qed.
Lemma lem5029911 {_113480 : Type'} (P : _113480 -> Prop) (x : _113480) : (term12 _113480 P x) = True.
Proof. exact (TRANS (@lem5029907 _113480 P x) (@lem5029910 _113480 P x)). Qed.
Lemma lem5029912 {_113480 : Type'} (P : _113480 -> Prop) : (term14 _113480 P) = (term15 _113480).
Proof. exact (fun_ext (fun x : _113480 => @lem5029911 _113480 P x)). Qed.
Lemma lem5029913 {_113480 : Type'} : (@all _113480) = (@all _113480).
Proof. exact (eq_refl (@all _113480)). Qed.
Lemma lem5029914 {_113480 : Type'} (P : _113480 -> Prop) : (term10 _113480 P) = (term16 _113480).
Proof. exact (MK_COMB (@lem5029913 _113480) (@lem5029912 _113480 P)). Qed.
Lemma lem5029916 {A : Type'} (t : Prop) : (term17 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5029917 {_113480 : Type'} (t : Prop) : (term17 _113480 t) = t.
Proof. exact (@lem5029916 _113480 t). Qed.
Lemma lem5029918 {_113480 : Type'} : (term16 _113480) = True.
Proof. exact (@lem5029917 _113480 True). Qed.
Lemma lem5029919 {_113480 : Type'} (P : _113480 -> Prop) : (term10 _113480 P) = True.
Proof. exact (TRANS (@lem5029914 _113480 P) (@lem5029918 _113480)). Qed.
Lemma lem5029920 {_113480 : Type'} (P : _113480 -> Prop) : ((term10 _113480 P) = True) = True.
Proof. exact (TRANS (@lem5029894 _113480 P) (@lem5029919 _113480 P)). Qed.
Lemma lem5029921 {_113480 : Type'} : (term18 _113480) = (term19 _113480).
Proof. exact (fun_ext (fun P : _113480 -> Prop => @lem5029920 _113480 P)). Qed.
Lemma lem5029922 {_113480 : Type'} : (@all (_113480 -> Prop)) = (@all (_113480 -> Prop)).
Proof. exact (eq_refl (@all (_113480 -> Prop))). Qed.
Lemma lem5029923 {_113480 : Type'} : (term20 _113480) = (term21 _113480).
Proof. exact (MK_COMB (@lem5029922 _113480) (@lem5029921 _113480)). Qed.
Lemma lem5029925 {A : Type'} (t : Prop) : (term17 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5029926 {_113480 : Type'} (t : Prop) : (term22 _113480 t) = t.
Proof. exact (@lem5029925 (_113480 -> Prop) t). Qed.
Lemma lem5029927 {_113480 : Type'} : (term21 _113480) = True.
Proof. exact (@lem5029926 _113480 True). Qed.
Lemma lem5029928 {_113480 : Type'} : (term20 _113480) = True.
Proof. exact (TRANS (@lem5029923 _113480) (@lem5029927 _113480)). Qed.
Lemma lem5029929 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5029930 {_113480 : Type'} : (term23 _113480) = (and True).
Proof. exact (MK_COMB (@lem5029929) (@lem5029928 _113480)). Qed.
Lemma lem5029952 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term8 A x y s) = (term9 A y x s).
Proof. exact (EQ_MP (@lem5029884 A y x s) (@lem5029883 A y x s)). Qed.
Lemma lem5029953 {_113520 : Type'} (y : _113520) (x : _113520) (s : _113520 -> Prop) : (term8 _113520 x y s) = (term9 _113520 y x s).
Proof. exact (@lem5029952 _113520 y x s). Qed.
Lemma lem5029954 {_113520 : Type'} (a : _113520) (x : _113520) (s : _113520 -> Prop) : (term8 _113520 x a s) = (term9 _113520 a x s).
Proof. exact (@lem5029953 _113520 a x s). Qed.
Lemma lem5029959 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5029960 {_113520 : Type'} (a : _113520) (x : _113520) (s : _113520 -> Prop) : (term24 _113520 x a s) = (term25 _113520 a x s).
Proof. exact (MK_COMB (@lem5029959) (@lem5029954 _113520 a x s)). Qed.
Lemma lem5029961 {_113520 : Type'} (P : _113520 -> Prop) (x : _113520) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem5029962 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term26 _113520 a s P x) = (term27 _113520 a s P x).
Proof. exact (MK_COMB (@lem5029960 _113520 a x s) (@lem5029961 _113520 P x)). Qed.
Lemma lem5029965 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term28 _113520 a s P) = (term29 _113520 a s P).
Proof. exact (fun_ext (fun x : _113520 => @lem5029962 _113520 a s P x)). Qed.
Lemma lem5029966 {_113520 : Type'} : (@all _113520) = (@all _113520).
Proof. exact (eq_refl (@all _113520)). Qed.
Lemma lem5029967 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term30 _113520 a s P) = (term31 _113520 a s P).
Proof. exact (MK_COMB (@lem5029966 _113520) (@lem5029965 _113520 a s P)). Qed.
Lemma lem5029972 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5029973 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term32 _113520 a s P) = (term33 _113520 a s P).
Proof. exact (MK_COMB (@lem5029972) (@lem5029967 _113520 a s P)). Qed.
Lemma lem5029982 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term34 _113520 a s P) = (term34 _113520 a s P).
Proof. exact (eq_refl (term34 _113520 a s P)). Qed.
Lemma lem5029983 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : ((term30 _113520 a s P) = (term34 _113520 a s P)) = ((term31 _113520 a s P) = (term34 _113520 a s P)).
Proof. exact (MK_COMB (@lem5029973 _113520 a s P) (@lem5029982 _113520 a s P)). Qed.
Lemma lem5029986 {_113520 : Type'} (a : _113520) (P : _113520 -> Prop) : (term35 _113520 a P) = (term36 _113520 a P).
Proof. exact (fun_ext (fun s : _113520 -> Prop => @lem5029983 _113520 a s P)). Qed.
Lemma lem5029987 {_113520 : Type'} : (@all (_113520 -> Prop)) = (@all (_113520 -> Prop)).
Proof. exact (eq_refl (@all (_113520 -> Prop))). Qed.
Lemma lem5029988 {_113520 : Type'} (a : _113520) (P : _113520 -> Prop) : (term37 _113520 a P) = (term38 _113520 a P).
Proof. exact (MK_COMB (@lem5029987 _113520) (@lem5029986 _113520 a P)). Qed.
Lemma lem5029993 {_113520 : Type'} (P : _113520 -> Prop) : (term39 _113520 P) = (term40 _113520 P).
Proof. exact (fun_ext (fun a : _113520 => @lem5029988 _113520 a P)). Qed.
Lemma lem5029994 {_113520 : Type'} : (@all _113520) = (@all _113520).
Proof. exact (eq_refl (@all _113520)). Qed.
Lemma lem5029995 {_113520 : Type'} (P : _113520 -> Prop) : (term41 _113520 P) = (term42 _113520 P).
Proof. exact (MK_COMB (@lem5029994 _113520) (@lem5029993 _113520 P)). Qed.
Lemma lem5030000 {_113520 : Type'} : (term43 _113520) = (term44 _113520).
Proof. exact (fun_ext (fun P : _113520 -> Prop => @lem5029995 _113520 P)). Qed.
Lemma lem5030001 {_113520 : Type'} : (@all (_113520 -> Prop)) = (@all (_113520 -> Prop)).
Proof. exact (eq_refl (@all (_113520 -> Prop))). Qed.
Lemma lem5030002 {_113520 : Type'} : (term45 _113520) = (term46 _113520).
Proof. exact (MK_COMB (@lem5030001 _113520) (@lem5030000 _113520)). Qed.
Lemma lem5030007 {_113480 _113520 : Type'} : (term47 _113480 _113520) = (term48 _113520).
Proof. exact (MK_COMB (@lem5029930 _113480) (@lem5030002 _113520)). Qed.
Lemma lem5030009 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5030010 {_113520 : Type'} : (term48 _113520) = (term46 _113520).
Proof. exact (@lem5030009 (term46 _113520)). Qed.
Lemma lem5030043 {_113480 _113520 : Type'} : (term47 _113480 _113520) = (term46 _113520).
Proof. exact (TRANS (@lem5030007 _113480 _113520) (@lem5030010 _113520)). Qed.
Lemma lem5030044 {_113480 _113520 : Type'} : (term46 _113520) = (term47 _113480 _113520).
Proof. exact (SYM (@lem5030043 _113480 _113520)). Qed.
Lemma lem5030046 (p : Prop) : p = (term49 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5030047 {_113520 : Type'} : (term46 _113520) = (term50 _113520).
Proof. exact (@lem5030046 (term46 _113520)). Qed.
Lemma lem5030048 {_113520 : Type'} : (term50 _113520) = (term46 _113520).
Proof. exact (SYM (@lem5030047 _113520)). Qed.
Lemma lem5030049 {_113520 : Type'} (h1 : term51 _113520) : term51 _113520.
Proof. exact (h1). Qed.
Lemma lem5030052 {_113520 : Type'} (h1 : term50 _113520) : term50 _113520.
Proof. exact (h1). Qed.
Lemma lem5030053 {_113520 : Type'} : term52 _113520.
Proof. exact (fun h0 : term50 _113520 => @lem5030052 _113520 h0). Qed.
Lemma lem5030054 {_113520 : Type'} (h1 : term52 _113520) : term52 _113520.
Proof. exact (h1). Qed.
Lemma lem5030055 {_113520 : Type'} (h1 : term50 _113520) : term50 _113520.
Proof. exact (h1). Qed.
Lemma lem5030056 {_113520 : Type'} (h1 : term50 _113520) (h2 : term52 _113520) : term50 _113520.
Proof. exact (@lem5030054 _113520 h2 (@lem5030055 _113520 h1)). Qed.
Lemma lem5030057 {_113520 : Type'} (h1 : term50 _113520) : term53 _113520.
Proof. exact (fun h0 : term52 _113520 => @lem5030056 _113520 h1 h0). Qed.
Lemma lem5030058 {_113520 : Type'} (h1 : term52 _113520) : term52 _113520.
Proof. exact (h1). Qed.
Lemma lem5030059 {_113520 : Type'} (h1 : term50 _113520) (h2 : term52 _113520) : term50 _113520.
Proof. exact (@lem5030057 _113520 h1 (@lem5030058 _113520 h2)). Qed.
Lemma lem5030060 {_113520 : Type'} (h1 : term52 _113520) : term52 _113520.
Proof. exact (fun h0 : term50 _113520 => @lem5030059 _113520 h0 h1). Qed.
Lemma lem5030061 {_113520 : Type'} : term54 _113520.
Proof. exact (fun h0 : term52 _113520 => @lem5030060 _113520 h0). Qed.
Lemma lem5030064 {_113520 : Type'} : term52 _113520.
Proof. exact (@lem5030061 _113520 (@lem5030053 _113520)). Qed.
Lemma lem5030065 {_113520 : Type'} : term52 _113520.
Proof. exact (@lem5030064 _113520). Qed.
Lemma lem5030067 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5030068 {_113520 : Type'} : (term50 _113520) = (term55 _113520).
Proof. exact (@lem5030067 (term51 _113520)). Qed.
Lemma lem5030070 (t : Prop) : (term56 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5030071 {_113520 : Type'} : (term55 _113520) = (term46 _113520).
Proof. exact (@lem5030070 (term46 _113520)). Qed.
Lemma lem5030104 {_113520 : Type'} : (term50 _113520) = (term46 _113520).
Proof. exact (TRANS (@lem5030068 _113520) (@lem5030071 _113520)). Qed.
Lemma lem5030109 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term57 _113520 s P x) = (term57 _113520 s P x).
Proof. exact (eq_refl (term57 _113520 s P x)). Qed.
Lemma lem5030110 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) : (term58 _113520 s P) = (term58 _113520 s P).
Proof. exact (fun_ext (fun x : _113520 => @lem5030109 _113520 s P x)). Qed.
Lemma lem5030111 {_113520 : Type'} : (@all _113520) = (@all _113520).
Proof. exact (eq_refl (@all _113520)). Qed.
Lemma lem5030112 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) : (term59 _113520 s P) = (term59 _113520 s P).
Proof. exact (MK_COMB (@lem5030111 _113520) (@lem5030110 _113520 s P)). Qed.
Lemma lem5030115 {_113520 : Type'} (P : _113520 -> Prop) (a : _113520) : (term60 _113520 P a) = (term60 _113520 P a).
Proof. exact (eq_refl (term60 _113520 P a)). Qed.
Lemma lem5030116 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term34 _113520 a s P) = (term34 _113520 a s P).
Proof. exact (MK_COMB (@lem5030115 _113520 P a) (@lem5030112 _113520 s P)). Qed.
Lemma lem5030125 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term27 _113520 a s P x) = (term27 _113520 a s P x).
Proof. exact (eq_refl (term27 _113520 a s P x)). Qed.
Lemma lem5030126 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term29 _113520 a s P) = (term29 _113520 a s P).
Proof. exact (fun_ext (fun x : _113520 => @lem5030125 _113520 a s P x)). Qed.
Lemma lem5030127 {_113520 : Type'} : (@all _113520) = (@all _113520).
Proof. exact (eq_refl (@all _113520)). Qed.
Lemma lem5030128 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term31 _113520 a s P) = (term31 _113520 a s P).
Proof. exact (MK_COMB (@lem5030127 _113520) (@lem5030126 _113520 a s P)). Qed.
Lemma lem5030129 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5030130 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term33 _113520 a s P) = (term33 _113520 a s P).
Proof. exact (MK_COMB (@lem5030129) (@lem5030128 _113520 a s P)). Qed.
Lemma lem5030131 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : ((term31 _113520 a s P) = (term34 _113520 a s P)) = ((term31 _113520 a s P) = (term34 _113520 a s P)).
Proof. exact (MK_COMB (@lem5030130 _113520 a s P) (@lem5030116 _113520 a s P)). Qed.
Lemma lem5030132 {_113520 : Type'} (a : _113520) (P : _113520 -> Prop) : (term36 _113520 a P) = (term36 _113520 a P).
Proof. exact (fun_ext (fun s : _113520 -> Prop => @lem5030131 _113520 a s P)). Qed.
Lemma lem5030133 {_113520 : Type'} : (@all (_113520 -> Prop)) = (@all (_113520 -> Prop)).
Proof. exact (eq_refl (@all (_113520 -> Prop))). Qed.
Lemma lem5030134 {_113520 : Type'} (a : _113520) (P : _113520 -> Prop) : (term38 _113520 a P) = (term38 _113520 a P).
Proof. exact (MK_COMB (@lem5030133 _113520) (@lem5030132 _113520 a P)). Qed.
Lemma lem5030135 {_113520 : Type'} (P : _113520 -> Prop) : (term40 _113520 P) = (term40 _113520 P).
Proof. exact (fun_ext (fun a : _113520 => @lem5030134 _113520 a P)). Qed.
Lemma lem5030136 {_113520 : Type'} : (@all _113520) = (@all _113520).
Proof. exact (eq_refl (@all _113520)). Qed.
Lemma lem5030137 {_113520 : Type'} (P : _113520 -> Prop) : (term42 _113520 P) = (term42 _113520 P).
Proof. exact (MK_COMB (@lem5030136 _113520) (@lem5030135 _113520 P)). Qed.
Lemma lem5030138 {_113520 : Type'} : (term44 _113520) = (term44 _113520).
Proof. exact (fun_ext (fun P : _113520 -> Prop => @lem5030137 _113520 P)). Qed.
Lemma lem5030139 {_113520 : Type'} : (@all (_113520 -> Prop)) = (@all (_113520 -> Prop)).
Proof. exact (eq_refl (@all (_113520 -> Prop))). Qed.
Lemma lem5030140 {_113520 : Type'} : (term46 _113520) = (term46 _113520).
Proof. exact (MK_COMB (@lem5030139 _113520) (@lem5030138 _113520)). Qed.
Lemma lem5030181 {_113520 : Type'} : (term50 _113520) = (term46 _113520).
Proof. exact (TRANS (@lem5030104 _113520) (@lem5030140 _113520)). Qed.
Lemma lem5030182 {_113520 : Type'} : (term46 _113520) = (term50 _113520).
Proof. exact (SYM (@lem5030181 _113520)). Qed.
Lemma lem5030184 (p : Prop) : p = (term49 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5030185 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : ((term31 _113520 a s P) = (term34 _113520 a s P)) = (term61 _113520 a s P).
Proof. exact (@lem5030184 ((term31 _113520 a s P) = (term34 _113520 a s P))). Qed.
Lemma lem5030186 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term61 _113520 a s P) = ((term31 _113520 a s P) = (term34 _113520 a s P)).
Proof. exact (SYM (@lem5030185 _113520 a s P)). Qed.
Lemma lem5030187 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (h1 : term62 _113520 a s P) : term62 _113520 a s P.
Proof. exact (h1). Qed.
Lemma lem5030196 {_113520 : Type'} (a : _113520) (x : _113520) (s : _113520 -> Prop) : (term63 _113520 a x s) = (term64 _113520 a x s).
Proof. exact (@lem17160 (x = a) (@IN _113520 x s)). Qed.
Lemma lem5030201 {_113520 : Type'} (P : _113520 -> Prop) (x : _113520) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem5030206 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term65 _113520 a s P x) = (term66 _113520 a s P x).
Proof. exact (@lem17362 (term9 _113520 a x s) (P x)). Qed.
Lemma lem5030207 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5030208 {_113520 : Type'} (a : _113520) (x : _113520) (s : _113520 -> Prop) : (term67 _113520 a x s) = (term68 _113520 a x s).
Proof. exact (MK_COMB (@lem5030207) (@lem5030196 _113520 a x s)). Qed.
Lemma lem5030209 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term69 _113520 a s P x) = (term70 _113520 a s P x).
Proof. exact (MK_COMB (@lem5030208 _113520 a x s) (@lem5030201 _113520 P x)). Qed.
Lemma lem5030210 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term27 _113520 a s P x) = (term69 _113520 a s P x).
Proof. exact (@lem17265 (term9 _113520 a x s) (P x)). Qed.
Lemma lem5030211 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term27 _113520 a s P x) = (term70 _113520 a s P x).
Proof. exact (TRANS (@lem5030210 _113520 a s P x) (@lem5030209 _113520 a s P x)). Qed.
Lemma lem5030212 {_113520 : Type'} (P : _113520 -> Prop) : (term71 _113520 P) = (term72 _113520 P).
Proof. exact (@lem18392 _113520 P). Qed.
Lemma lem5030213 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term73 _113520 a s P) = (term74 _113520 a s P).
Proof. exact (@lem5030212 _113520 (term29 _113520 a s P)). Qed.
Lemma lem5030214 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term75 _113520 a s P x) = (term27 _113520 a s P x).
Proof. exact (eq_refl (term75 _113520 a s P x)). Qed.
Lemma lem5030215 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5030216 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term76 _113520 a s P x) = (term65 _113520 a s P x).
Proof. exact (MK_COMB (@lem5030215) (@lem5030214 _113520 a s P x)). Qed.
Lemma lem5030217 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term76 _113520 a s P x) = (term66 _113520 a s P x).
Proof. exact (TRANS (@lem5030216 _113520 a s P x) (@lem5030206 _113520 a s P x)). Qed.
Lemma lem5030218 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term77 _113520 a s P) = (term78 _113520 a s P).
Proof. exact (fun_ext (fun x : _113520 => @lem5030217 _113520 a s P x)). Qed.
Lemma lem5030219 {_113520 : Type'} : (@ex _113520) = (@ex _113520).
Proof. exact (eq_refl (@ex _113520)). Qed.
Lemma lem5030220 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term74 _113520 a s P) = (term79 _113520 a s P).
Proof. exact (MK_COMB (@lem5030219 _113520) (@lem5030218 _113520 a s P)). Qed.
Lemma lem5030221 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term73 _113520 a s P) = (term79 _113520 a s P).
Proof. exact (TRANS (@lem5030213 _113520 a s P) (@lem5030220 _113520 a s P)). Qed.
Lemma lem5030222 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term29 _113520 a s P) = (term80 _113520 a s P).
Proof. exact (fun_ext (fun x : _113520 => @lem5030211 _113520 a s P x)). Qed.
Lemma lem5030223 {_113520 : Type'} : (@all _113520) = (@all _113520).
Proof. exact (eq_refl (@all _113520)). Qed.
Lemma lem5030224 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term31 _113520 a s P) = (term81 _113520 a s P).
Proof. exact (MK_COMB (@lem5030223 _113520) (@lem5030222 _113520 a s P)). Qed.
Lemma lem5030235 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term82 _113520 s P x) = (term83 _113520 s P x).
Proof. exact (@lem17362 (@IN _113520 x s) (P x)). Qed.
Lemma lem5030240 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term57 _113520 s P x) = (term84 _113520 s P x).
Proof. exact (@lem17265 (@IN _113520 x s) (P x)). Qed.
Lemma lem5030241 {_113520 : Type'} (P : _113520 -> Prop) : (term71 _113520 P) = (term72 _113520 P).
Proof. exact (@lem18392 _113520 P). Qed.
Lemma lem5030242 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) : (term85 _113520 s P) = (term86 _113520 s P).
Proof. exact (@lem5030241 _113520 (term58 _113520 s P)). Qed.
Lemma lem5030243 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term87 _113520 s P x) = (term57 _113520 s P x).
Proof. exact (eq_refl (term87 _113520 s P x)). Qed.
Lemma lem5030244 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5030245 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term88 _113520 s P x) = (term82 _113520 s P x).
Proof. exact (MK_COMB (@lem5030244) (@lem5030243 _113520 s P x)). Qed.
Lemma lem5030246 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term88 _113520 s P x) = (term83 _113520 s P x).
Proof. exact (TRANS (@lem5030245 _113520 s P x) (@lem5030235 _113520 s P x)). Qed.
Lemma lem5030247 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) : (term89 _113520 s P) = (term90 _113520 s P).
Proof. exact (fun_ext (fun x : _113520 => @lem5030246 _113520 s P x)). Qed.
Lemma lem5030248 {_113520 : Type'} : (@ex _113520) = (@ex _113520).
Proof. exact (eq_refl (@ex _113520)). Qed.
Lemma lem5030249 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) : (term86 _113520 s P) = (term91 _113520 s P).
Proof. exact (MK_COMB (@lem5030248 _113520) (@lem5030247 _113520 s P)). Qed.
Lemma lem5030250 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) : (term85 _113520 s P) = (term91 _113520 s P).
Proof. exact (TRANS (@lem5030242 _113520 s P) (@lem5030249 _113520 s P)). Qed.
Lemma lem5030251 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) : (term58 _113520 s P) = (term92 _113520 s P).
Proof. exact (fun_ext (fun x : _113520 => @lem5030240 _113520 s P x)). Qed.
Lemma lem5030252 {_113520 : Type'} : (@all _113520) = (@all _113520).
Proof. exact (eq_refl (@all _113520)). Qed.
Lemma lem5030253 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) : (term59 _113520 s P) = (term93 _113520 s P).
Proof. exact (MK_COMB (@lem5030252 _113520) (@lem5030251 _113520 s P)). Qed.
Lemma lem5030255 {_113520 : Type'} (P : _113520 -> Prop) (a : _113520) : (term94 _113520 P a) = (term94 _113520 P a).
Proof. exact (eq_refl (term94 _113520 P a)). Qed.
Lemma lem5030256 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term95 _113520 a s P) = (term96 _113520 a s P).
Proof. exact (MK_COMB (@lem5030255 _113520 P a) (@lem5030250 _113520 s P)). Qed.
Lemma lem5030257 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term97 _113520 a s P) = (term95 _113520 a s P).
Proof. exact (@lem17045 (P a) (term59 _113520 s P)). Qed.
Lemma lem5030258 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term97 _113520 a s P) = (term96 _113520 a s P).
Proof. exact (TRANS (@lem5030257 _113520 a s P) (@lem5030256 _113520 a s P)). Qed.
Lemma lem5030260 {_113520 : Type'} (P : _113520 -> Prop) (a : _113520) : (term60 _113520 P a) = (term60 _113520 P a).
Proof. exact (eq_refl (term60 _113520 P a)). Qed.
Lemma lem5030261 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term34 _113520 a s P) = (term98 _113520 a s P).
Proof. exact (MK_COMB (@lem5030260 _113520 P a) (@lem5030253 _113520 s P)). Qed.
Lemma lem5030262 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5030263 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term99 _113520 a s P) = (term100 _113520 a s P).
Proof. exact (MK_COMB (@lem5030262) (@lem5030221 _113520 a s P)). Qed.
Lemma lem5030264 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term101 _113520 a s P) = (term102 _113520 a s P).
Proof. exact (MK_COMB (@lem5030263 _113520 a s P) (@lem5030261 _113520 a s P)). Qed.
Lemma lem5030265 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5030266 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term103 _113520 a s P) = (term104 _113520 a s P).
Proof. exact (MK_COMB (@lem5030265) (@lem5030224 _113520 a s P)). Qed.
Lemma lem5030267 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term105 _113520 a s P) = (term106 _113520 a s P).
Proof. exact (MK_COMB (@lem5030266 _113520 a s P) (@lem5030258 _113520 a s P)). Qed.
Lemma lem5030268 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5030269 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term107 _113520 a s P) = (term108 _113520 a s P).
Proof. exact (MK_COMB (@lem5030268) (@lem5030267 _113520 a s P)). Qed.
Lemma lem5030270 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term109 _113520 a s P) = (term110 _113520 a s P).
Proof. exact (MK_COMB (@lem5030269 _113520 a s P) (@lem5030264 _113520 a s P)). Qed.
Lemma lem5030271 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term62 _113520 a s P) = (term109 _113520 a s P).
Proof. exact (@lem17646 (term31 _113520 a s P) (term34 _113520 a s P)). Qed.
Lemma lem5030272 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term62 _113520 a s P) = (term110 _113520 a s P).
Proof. exact (TRANS (@lem5030271 _113520 a s P) (@lem5030270 _113520 a s P)). Qed.
Lemma lem5030435 {A : Type'} (P : Prop) (Q : A -> Prop) : (term111 A P Q) = (term112 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5030436 {_113520 : Type'} (P : Prop) (Q : _113520 -> Prop) : (term111 _113520 P Q) = (term112 _113520 P Q).
Proof. exact (@lem5030435 _113520 P Q). Qed.
Lemma lem5030437 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term113 _113520 a s P) = (term114 _113520 a s P).
Proof. exact (@lem5030436 _113520 (term115 _113520 P a) (term90 _113520 s P)). Qed.
Lemma lem5030438 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term116 _113520 s P x) = (term83 _113520 s P x).
Proof. exact (eq_refl (term116 _113520 s P x)). Qed.
Lemma lem5030439 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) : (term117 _113520 s P) = (term90 _113520 s P).
Proof. exact (fun_ext (fun x : _113520 => @lem5030438 _113520 s P x)). Qed.
Lemma lem5030440 {_113520 : Type'} : (@ex _113520) = (@ex _113520).
Proof. exact (eq_refl (@ex _113520)). Qed.
Lemma lem5030441 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) : (term118 _113520 s P) = (term91 _113520 s P).
Proof. exact (MK_COMB (@lem5030440 _113520) (@lem5030439 _113520 s P)). Qed.
Lemma lem5030442 {_113520 : Type'} (P : _113520 -> Prop) (a : _113520) : (term94 _113520 P a) = (term94 _113520 P a).
Proof. exact (eq_refl (term94 _113520 P a)). Qed.
Lemma lem5030443 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term113 _113520 a s P) = (term96 _113520 a s P).
Proof. exact (MK_COMB (@lem5030442 _113520 P a) (@lem5030441 _113520 s P)). Qed.
Lemma lem5030444 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5030445 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term119 _113520 a s P) = (term120 _113520 a s P).
Proof. exact (MK_COMB (@lem5030444) (@lem5030443 _113520 a s P)). Qed.
Lemma lem5030446 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term116 _113520 s P x) = (term83 _113520 s P x).
Proof. exact (eq_refl (term116 _113520 s P x)). Qed.
Lemma lem5030447 {_113520 : Type'} (P : _113520 -> Prop) (a : _113520) : (term94 _113520 P a) = (term94 _113520 P a).
Proof. exact (eq_refl (term94 _113520 P a)). Qed.
Lemma lem5030448 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term121 _113520 a s P x) = (term122 _113520 a s P x).
Proof. exact (MK_COMB (@lem5030447 _113520 P a) (@lem5030446 _113520 s P x)). Qed.
Lemma lem5030449 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term123 _113520 a s P) = (term124 _113520 a s P).
Proof. exact (fun_ext (fun x : _113520 => @lem5030448 _113520 a s P x)). Qed.
Lemma lem5030450 {_113520 : Type'} : (@ex _113520) = (@ex _113520).
Proof. exact (eq_refl (@ex _113520)). Qed.
Lemma lem5030451 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term114 _113520 a s P) = (term125 _113520 a s P).
Proof. exact (MK_COMB (@lem5030450 _113520) (@lem5030449 _113520 a s P)). Qed.
Lemma lem5030452 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : ((term113 _113520 a s P) = (term114 _113520 a s P)) = ((term96 _113520 a s P) = (term125 _113520 a s P)).
Proof. exact (MK_COMB (@lem5030445 _113520 a s P) (@lem5030451 _113520 a s P)). Qed.
Lemma lem5030453 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term96 _113520 a s P) = (term125 _113520 a s P).
Proof. exact (EQ_MP (@lem5030452 _113520 a s P) (@lem5030437 _113520 a s P)). Qed.
Lemma lem5030454 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term104 _113520 a s P) = (term104 _113520 a s P).
Proof. exact (eq_refl (term104 _113520 a s P)). Qed.
Lemma lem5030455 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term106 _113520 a s P) = (term126 _113520 a s P).
Proof. exact (MK_COMB (@lem5030454 _113520 a s P) (@lem5030453 _113520 a s P)). Qed.
Lemma lem5030457 {A : Type'} (P : Prop) (Q : A -> Prop) : (term127 A P Q) = (term128 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5030458 {_113520 : Type'} (P : Prop) (Q : _113520 -> Prop) : (term127 _113520 P Q) = (term128 _113520 P Q).
Proof. exact (@lem5030457 _113520 P Q). Qed.
Lemma lem5030459 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term129 _113520 a s P) = (term130 _113520 a s P).
Proof. exact (@lem5030458 _113520 (term81 _113520 a s P) (term124 _113520 a s P)). Qed.
Lemma lem5030460 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term131 _113520 a s P x) = (term122 _113520 a s P x).
Proof. exact (eq_refl (term131 _113520 a s P x)). Qed.
Lemma lem5030461 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term132 _113520 a s P) = (term124 _113520 a s P).
Proof. exact (fun_ext (fun x : _113520 => @lem5030460 _113520 a s P x)). Qed.
Lemma lem5030462 {_113520 : Type'} : (@ex _113520) = (@ex _113520).
Proof. exact (eq_refl (@ex _113520)). Qed.
Lemma lem5030463 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term133 _113520 a s P) = (term125 _113520 a s P).
Proof. exact (MK_COMB (@lem5030462 _113520) (@lem5030461 _113520 a s P)). Qed.
Lemma lem5030464 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term104 _113520 a s P) = (term104 _113520 a s P).
Proof. exact (eq_refl (term104 _113520 a s P)). Qed.
Lemma lem5030465 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term129 _113520 a s P) = (term126 _113520 a s P).
Proof. exact (MK_COMB (@lem5030464 _113520 a s P) (@lem5030463 _113520 a s P)). Qed.
Lemma lem5030466 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5030467 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term134 _113520 a s P) = (term135 _113520 a s P).
Proof. exact (MK_COMB (@lem5030466) (@lem5030465 _113520 a s P)). Qed.
Lemma lem5030468 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term131 _113520 a s P x) = (term122 _113520 a s P x).
Proof. exact (eq_refl (term131 _113520 a s P x)). Qed.
Lemma lem5030469 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term104 _113520 a s P) = (term104 _113520 a s P).
Proof. exact (eq_refl (term104 _113520 a s P)). Qed.
Lemma lem5030470 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term136 _113520 a s P x) = (term137 _113520 a s P x).
Proof. exact (MK_COMB (@lem5030469 _113520 a s P) (@lem5030468 _113520 a s P x)). Qed.
Lemma lem5030471 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term138 _113520 a s P) = (term139 _113520 a s P).
Proof. exact (fun_ext (fun x : _113520 => @lem5030470 _113520 a s P x)). Qed.
Lemma lem5030472 {_113520 : Type'} : (@ex _113520) = (@ex _113520).
Proof. exact (eq_refl (@ex _113520)). Qed.
Lemma lem5030473 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term130 _113520 a s P) = (term140 _113520 a s P).
Proof. exact (MK_COMB (@lem5030472 _113520) (@lem5030471 _113520 a s P)). Qed.
Lemma lem5030474 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : ((term129 _113520 a s P) = (term130 _113520 a s P)) = ((term126 _113520 a s P) = (term140 _113520 a s P)).
Proof. exact (MK_COMB (@lem5030467 _113520 a s P) (@lem5030473 _113520 a s P)). Qed.
Lemma lem5030475 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term126 _113520 a s P) = (term140 _113520 a s P).
Proof. exact (EQ_MP (@lem5030474 _113520 a s P) (@lem5030459 _113520 a s P)). Qed.
Lemma lem5030476 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term106 _113520 a s P) = (term140 _113520 a s P).
Proof. exact (TRANS (@lem5030455 _113520 a s P) (@lem5030475 _113520 a s P)). Qed.
Lemma lem5030477 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5030478 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term108 _113520 a s P) = (term141 _113520 a s P).
Proof. exact (MK_COMB (@lem5030477) (@lem5030476 _113520 a s P)). Qed.
Lemma lem5030480 {A : Type'} (P : A -> Prop) (Q : Prop) : (term142 A P Q) = (term143 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5030481 {_113520 : Type'} (P : _113520 -> Prop) (Q : Prop) : (term142 _113520 P Q) = (term143 _113520 P Q).
Proof. exact (@lem5030480 _113520 P Q). Qed.
Lemma lem5030482 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term144 _113520 a s P) = (term145 _113520 a s P).
Proof. exact (@lem5030481 _113520 (term78 _113520 a s P) (term98 _113520 a s P)). Qed.
Lemma lem5030483 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term146 _113520 a s P x) = (term66 _113520 a s P x).
Proof. exact (eq_refl (term146 _113520 a s P x)). Qed.
Lemma lem5030484 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term147 _113520 a s P) = (term78 _113520 a s P).
Proof. exact (fun_ext (fun x : _113520 => @lem5030483 _113520 a s P x)). Qed.
Lemma lem5030485 {_113520 : Type'} : (@ex _113520) = (@ex _113520).
Proof. exact (eq_refl (@ex _113520)). Qed.
Lemma lem5030486 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term148 _113520 a s P) = (term79 _113520 a s P).
Proof. exact (MK_COMB (@lem5030485 _113520) (@lem5030484 _113520 a s P)). Qed.
Lemma lem5030487 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5030488 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term149 _113520 a s P) = (term100 _113520 a s P).
Proof. exact (MK_COMB (@lem5030487) (@lem5030486 _113520 a s P)). Qed.
Lemma lem5030489 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term98 _113520 a s P) = (term98 _113520 a s P).
Proof. exact (eq_refl (term98 _113520 a s P)). Qed.
Lemma lem5030490 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term144 _113520 a s P) = (term102 _113520 a s P).
Proof. exact (MK_COMB (@lem5030488 _113520 a s P) (@lem5030489 _113520 a s P)). Qed.
Lemma lem5030491 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5030492 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term150 _113520 a s P) = (term151 _113520 a s P).
Proof. exact (MK_COMB (@lem5030491) (@lem5030490 _113520 a s P)). Qed.
Lemma lem5030493 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term146 _113520 a s P x) = (term66 _113520 a s P x).
Proof. exact (eq_refl (term146 _113520 a s P x)). Qed.
Lemma lem5030494 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5030495 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term152 _113520 a s P x) = (term153 _113520 a s P x).
Proof. exact (MK_COMB (@lem5030494) (@lem5030493 _113520 a s P x)). Qed.
Lemma lem5030496 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term98 _113520 a s P) = (term98 _113520 a s P).
Proof. exact (eq_refl (term98 _113520 a s P)). Qed.
Lemma lem5030497 {_113520 : Type'} (x : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term154 _113520 x a s P) = (term155 _113520 x a s P).
Proof. exact (MK_COMB (@lem5030495 _113520 a s P x) (@lem5030496 _113520 a s P)). Qed.
Lemma lem5030498 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term156 _113520 a s P) = (term157 _113520 a s P).
Proof. exact (fun_ext (fun x : _113520 => @lem5030497 _113520 x a s P)). Qed.
Lemma lem5030499 {_113520 : Type'} : (@ex _113520) = (@ex _113520).
Proof. exact (eq_refl (@ex _113520)). Qed.
Lemma lem5030500 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term145 _113520 a s P) = (term158 _113520 a s P).
Proof. exact (MK_COMB (@lem5030499 _113520) (@lem5030498 _113520 a s P)). Qed.
Lemma lem5030501 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : ((term144 _113520 a s P) = (term145 _113520 a s P)) = ((term102 _113520 a s P) = (term158 _113520 a s P)).
Proof. exact (MK_COMB (@lem5030492 _113520 a s P) (@lem5030500 _113520 a s P)). Qed.
Lemma lem5030502 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term102 _113520 a s P) = (term158 _113520 a s P).
Proof. exact (EQ_MP (@lem5030501 _113520 a s P) (@lem5030482 _113520 a s P)). Qed.
Lemma lem5030503 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term110 _113520 a s P) = (term159 _113520 a s P).
Proof. exact (MK_COMB (@lem5030478 _113520 a s P) (@lem5030502 _113520 a s P)). Qed.
Lemma lem5030505 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term160 A P Q) = (term161 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5030506 {_113520 : Type'} (P : _113520 -> Prop) (Q : _113520 -> Prop) : (term160 _113520 P Q) = (term161 _113520 P Q).
Proof. exact (@lem5030505 _113520 P Q). Qed.
Lemma lem5030507 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term162 _113520 a s P) = (term163 _113520 a s P).
Proof. exact (@lem5030506 _113520 (term139 _113520 a s P) (term157 _113520 a s P)). Qed.
Lemma lem5030508 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term164 _113520 a s P x) = (term137 _113520 a s P x).
Proof. exact (eq_refl (term164 _113520 a s P x)). Qed.
Lemma lem5030509 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term165 _113520 a s P) = (term139 _113520 a s P).
Proof. exact (fun_ext (fun x : _113520 => @lem5030508 _113520 a s P x)). Qed.
Lemma lem5030510 {_113520 : Type'} : (@ex _113520) = (@ex _113520).
Proof. exact (eq_refl (@ex _113520)). Qed.
Lemma lem5030511 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term166 _113520 a s P) = (term140 _113520 a s P).
Proof. exact (MK_COMB (@lem5030510 _113520) (@lem5030509 _113520 a s P)). Qed.
Lemma lem5030512 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5030513 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term167 _113520 a s P) = (term141 _113520 a s P).
Proof. exact (MK_COMB (@lem5030512) (@lem5030511 _113520 a s P)). Qed.
Lemma lem5030514 {_113520 : Type'} (x : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term168 _113520 a s P x) = (term155 _113520 x a s P).
Proof. exact (eq_refl (term168 _113520 a s P x)). Qed.
Lemma lem5030515 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term169 _113520 a s P) = (term157 _113520 a s P).
Proof. exact (fun_ext (fun x : _113520 => @lem5030514 _113520 x a s P)). Qed.
Lemma lem5030516 {_113520 : Type'} : (@ex _113520) = (@ex _113520).
Proof. exact (eq_refl (@ex _113520)). Qed.
Lemma lem5030517 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term170 _113520 a s P) = (term158 _113520 a s P).
Proof. exact (MK_COMB (@lem5030516 _113520) (@lem5030515 _113520 a s P)). Qed.
Lemma lem5030518 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term162 _113520 a s P) = (term159 _113520 a s P).
Proof. exact (MK_COMB (@lem5030513 _113520 a s P) (@lem5030517 _113520 a s P)). Qed.
Lemma lem5030519 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5030520 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term171 _113520 a s P) = (term172 _113520 a s P).
Proof. exact (MK_COMB (@lem5030519) (@lem5030518 _113520 a s P)). Qed.
Lemma lem5030521 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term164 _113520 a s P x) = (term137 _113520 a s P x).
Proof. exact (eq_refl (term164 _113520 a s P x)). Qed.
Lemma lem5030522 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5030523 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term173 _113520 a s P x) = (term174 _113520 a s P x).
Proof. exact (MK_COMB (@lem5030522) (@lem5030521 _113520 a s P x)). Qed.
Lemma lem5030524 {_113520 : Type'} (x : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term168 _113520 a s P x) = (term155 _113520 x a s P).
Proof. exact (eq_refl (term168 _113520 a s P x)). Qed.
Lemma lem5030525 {_113520 : Type'} (x : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term175 _113520 a s P x) = (term176 _113520 x a s P).
Proof. exact (MK_COMB (@lem5030523 _113520 a s P x) (@lem5030524 _113520 x a s P)). Qed.
Lemma lem5030526 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term177 _113520 a s P) = (term178 _113520 a s P).
Proof. exact (fun_ext (fun x : _113520 => @lem5030525 _113520 x a s P)). Qed.
Lemma lem5030527 {_113520 : Type'} : (@ex _113520) = (@ex _113520).
Proof. exact (eq_refl (@ex _113520)). Qed.
Lemma lem5030528 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term163 _113520 a s P) = (term179 _113520 a s P).
Proof. exact (MK_COMB (@lem5030527 _113520) (@lem5030526 _113520 a s P)). Qed.
Lemma lem5030529 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : ((term162 _113520 a s P) = (term163 _113520 a s P)) = ((term159 _113520 a s P) = (term179 _113520 a s P)).
Proof. exact (MK_COMB (@lem5030520 _113520 a s P) (@lem5030528 _113520 a s P)). Qed.
Lemma lem5030530 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term159 _113520 a s P) = (term179 _113520 a s P).
Proof. exact (EQ_MP (@lem5030529 _113520 a s P) (@lem5030507 _113520 a s P)). Qed.
Lemma lem5030532 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term110 _113520 a s P) = (term179 _113520 a s P).
Proof. exact (TRANS (@lem5030503 _113520 a s P) (@lem5030530 _113520 a s P)). Qed.
Lemma lem5030533 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term62 _113520 a s P) = (term179 _113520 a s P).
Proof. exact (TRANS (@lem5030272 _113520 a s P) (@lem5030532 _113520 a s P)). Qed.
Lemma lem5030534 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (h1 : term62 _113520 a s P) : term179 _113520 a s P.
Proof. exact (EQ_MP (@lem5030533 _113520 a s P) (@lem5030187 _113520 a s P h1)). Qed.
Lemma lem5030535 {_113520 : Type'} (x : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (h1 : term176 _113520 x a s P) : term176 _113520 x a s P.
Proof. exact (h1). Qed.
Lemma lem5030548 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term84 _113520 s P x) = (term84 _113520 s P x).
Proof. exact (eq_refl (term84 _113520 s P x)). Qed.
Lemma lem5030549 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) : (term92 _113520 s P) = (term92 _113520 s P).
Proof. exact (fun_ext (fun x : _113520 => @lem5030548 _113520 s P x)). Qed.
Lemma lem5030550 {_113520 : Type'} : (@all _113520) = (@all _113520).
Proof. exact (eq_refl (@all _113520)). Qed.
Lemma lem5030551 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) : (term93 _113520 s P) = (term93 _113520 s P).
Proof. exact (MK_COMB (@lem5030550 _113520) (@lem5030549 _113520 s P)). Qed.
Lemma lem5030556 {_113520 : Type'} (P : _113520 -> Prop) (a : _113520) : (term60 _113520 P a) = (term60 _113520 P a).
Proof. exact (eq_refl (term60 _113520 P a)). Qed.
Lemma lem5030557 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term98 _113520 a s P) = (term98 _113520 a s P).
Proof. exact (MK_COMB (@lem5030556 _113520 P a) (@lem5030551 _113520 s P)). Qed.
Lemma lem5030580 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term153 _113520 a s P x) = (term153 _113520 a s P x).
Proof. exact (eq_refl (term153 _113520 a s P x)). Qed.
Lemma lem5030581 {_113520 : Type'} (x : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term155 _113520 x a s P) = (term155 _113520 x a s P).
Proof. exact (MK_COMB (@lem5030580 _113520 a s P x) (@lem5030557 _113520 a s P)). Qed.
Lemma lem5030602 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term122 _113520 a s P x) = (term122 _113520 a s P x).
Proof. exact (eq_refl (term122 _113520 a s P x)). Qed.
Lemma lem5030625 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term70 _113520 a s P x) = (term70 _113520 a s P x).
Proof. exact (eq_refl (term70 _113520 a s P x)). Qed.
Lemma lem5030626 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term80 _113520 a s P) = (term80 _113520 a s P).
Proof. exact (fun_ext (fun x : _113520 => @lem5030625 _113520 a s P x)). Qed.
Lemma lem5030627 {_113520 : Type'} : (@all _113520) = (@all _113520).
Proof. exact (eq_refl (@all _113520)). Qed.
Lemma lem5030628 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term81 _113520 a s P) = (term81 _113520 a s P).
Proof. exact (MK_COMB (@lem5030627 _113520) (@lem5030626 _113520 a s P)). Qed.
Lemma lem5030629 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5030630 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term104 _113520 a s P) = (term104 _113520 a s P).
Proof. exact (MK_COMB (@lem5030629) (@lem5030628 _113520 a s P)). Qed.
Lemma lem5030631 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term137 _113520 a s P x) = (term137 _113520 a s P x).
Proof. exact (MK_COMB (@lem5030630 _113520 a s P) (@lem5030602 _113520 a s P x)). Qed.
Lemma lem5030632 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5030633 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term174 _113520 a s P x) = (term174 _113520 a s P x).
Proof. exact (MK_COMB (@lem5030632) (@lem5030631 _113520 a s P x)). Qed.
Lemma lem5030634 {_113520 : Type'} (x : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term176 _113520 x a s P) = (term176 _113520 x a s P).
Proof. exact (MK_COMB (@lem5030633 _113520 a s P x) (@lem5030581 _113520 x a s P)). Qed.
Lemma lem5030635 {_113520 : Type'} (x : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (h1 : term176 _113520 x a s P) : term176 _113520 x a s P.
Proof. exact (EQ_MP (@lem5030634 _113520 x a s P) (@lem5030535 _113520 x a s P h1)). Qed.
Lemma lem5030636 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term137 _113520 a s P x) : term137 _113520 a s P x.
Proof. exact (h1). Qed.
Lemma lem5030637 {_113520 : Type'} (x : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (h1 : term155 _113520 x a s P) : term155 _113520 x a s P.
Proof. exact (h1). Qed.
Lemma lem5030638 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term137 _113520 a s P x) : term122 _113520 a s P x.
Proof. exact (proj2 (@lem5030636 _113520 a s P x h1)). Qed.
Lemma lem5030639 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term137 _113520 a s P x) : term81 _113520 a s P.
Proof. exact (proj1 (@lem5030636 _113520 a s P x h1)). Qed.
Lemma lem5030641 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term83 _113520 s P x) : term83 _113520 s P x.
Proof. exact (h1). Qed.
Lemma lem5030644 {_113520 : Type'} (x : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (h1 : term155 _113520 x a s P) : term98 _113520 a s P.
Proof. exact (proj2 (@lem5030637 _113520 x a s P h1)). Qed.
Lemma lem5030645 {_113520 : Type'} (x : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (h1 : term155 _113520 x a s P) : term66 _113520 a s P x.
Proof. exact (proj1 (@lem5030637 _113520 x a s P h1)). Qed.
Lemma lem5030646 {_113520 : Type'} (x : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (h1 : term155 _113520 x a s P) : term93 _113520 s P.
Proof. exact (proj2 (@lem5030644 _113520 x a s P h1)). Qed.
Lemma lem5030649 {_113520 : Type'} (x : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (h1 : term155 _113520 x a s P) : term9 _113520 a x s.
Proof. exact (proj1 (@lem5030645 _113520 x a s P h1)). Qed.
Lemma lem5030669 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term70 _113520 a s P x) = (term180 _113520 a s P x).
Proof. exact (@lem19699 (term181 _113520 x a) (term182 _113520 x s) (P x)). Qed.
Lemma lem5030670 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term80 _113520 a s P) = (term183 _113520 a s P).
Proof. exact (fun_ext (fun x : _113520 => @lem5030669 _113520 a s P x)). Qed.
Lemma lem5030671 {_113520 : Type'} : (@all _113520) = (@all _113520).
Proof. exact (eq_refl (@all _113520)). Qed.
Lemma lem5030673 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term81 _113520 a s P) = (term184 _113520 a s P).
Proof. exact (MK_COMB (@lem5030671 _113520) (@lem5030670 _113520 a s P)). Qed.
Lemma lem5030674 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term137 _113520 a s P x) : term184 _113520 a s P.
Proof. exact (EQ_MP (@lem5030673 _113520 a s P) (@lem5030639 _113520 a s P x h1)). Qed.
Lemma lem5030678 {_113520 : Type'} (P : _113520 -> Prop) (a : _113520) (h1 : term115 _113520 P a) : term115 _113520 P a.
Proof. exact (h1). Qed.
Lemma lem5030696 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term70 _113520 a s P x) = (term180 _113520 a s P x).
Proof. exact (@lem19699 (term181 _113520 x a) (term182 _113520 x s) (P x)). Qed.
Lemma lem5030697 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term80 _113520 a s P) = (term183 _113520 a s P).
Proof. exact (fun_ext (fun x : _113520 => @lem5030696 _113520 a s P x)). Qed.
Lemma lem5030698 {_113520 : Type'} : (@all _113520) = (@all _113520).
Proof. exact (eq_refl (@all _113520)). Qed.
Lemma lem5030700 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term81 _113520 a s P) = (term184 _113520 a s P).
Proof. exact (MK_COMB (@lem5030698 _113520) (@lem5030697 _113520 a s P)). Qed.
Lemma lem5030701 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term137 _113520 a s P x) : term184 _113520 a s P.
Proof. exact (EQ_MP (@lem5030700 _113520 a s P) (@lem5030639 _113520 a s P x h1)). Qed.
Lemma lem5030734 {_113520 : Type'} (x : _113520) (a : _113520) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem5030746 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) : (term84 _113520 s P x) = (term84 _113520 s P x).
Proof. exact (eq_refl (term84 _113520 s P x)). Qed.
Lemma lem5030747 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) : (term92 _113520 s P) = (term92 _113520 s P).
Proof. exact (fun_ext (fun x : _113520 => @lem5030746 _113520 s P x)). Qed.
Lemma lem5030748 {_113520 : Type'} : (@all _113520) = (@all _113520).
Proof. exact (eq_refl (@all _113520)). Qed.
Lemma lem5030750 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) : (term93 _113520 s P) = (term93 _113520 s P).
Proof. exact (MK_COMB (@lem5030748 _113520) (@lem5030747 _113520 s P)). Qed.
Lemma lem5030751 {_113520 : Type'} (x : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (h1 : term155 _113520 x a s P) : term93 _113520 s P.
Proof. exact (EQ_MP (@lem5030750 _113520 s P) (@lem5030646 _113520 x a s P h1)). Qed.
Lemma lem5030759 {_113520 : Type'} (x : _113520) (s : _113520 -> Prop) (h1 : @IN _113520 x s) : @IN _113520 x s.
Proof. exact (h1). Qed.
Lemma lem5030760 {_113520 : Type'} (_64644 : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term137 _113520 a s P x) : term185 _113520 a s P _64644.
Proof. exact (@lem5030674 _113520 a s P x h1 _64644). Qed.
Lemma lem5030761 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (_64644 : _113520) : (term185 _113520 a s P _64644) = (term180 _113520 a s P _64644).
Proof. exact (eq_refl (term185 _113520 a s P _64644)). Qed.
Lemma lem5030762 {_113520 : Type'} (_64644 : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term137 _113520 a s P x) : term180 _113520 a s P _64644.
Proof. exact (EQ_MP (@lem5030761 _113520 a s P _64644) (@lem5030760 _113520 _64644 a s P x h1)). Qed.
Lemma lem5030763 {_113520 : Type'} (_64645 : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term137 _113520 a s P x) : term185 _113520 a s P _64645.
Proof. exact (@lem5030701 _113520 a s P x h1 _64645). Qed.
Lemma lem5030764 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (_64645 : _113520) : (term185 _113520 a s P _64645) = (term180 _113520 a s P _64645).
Proof. exact (eq_refl (term185 _113520 a s P _64645)). Qed.
Lemma lem5030765 {_113520 : Type'} (_64645 : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term137 _113520 a s P x) : term180 _113520 a s P _64645.
Proof. exact (EQ_MP (@lem5030764 _113520 a s P _64645) (@lem5030763 _113520 _64645 a s P x h1)). Qed.
Lemma lem5030769 {_113520 : Type'} (_64647 : _113520) (x : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (h1 : term155 _113520 x a s P) : term186 _113520 s P _64647.
Proof. exact (@lem5030751 _113520 x a s P h1 _64647). Qed.
Lemma lem5030770 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (_64647 : _113520) : (term186 _113520 s P _64647) = (term84 _113520 s P _64647).
Proof. exact (eq_refl (term186 _113520 s P _64647)). Qed.
Lemma lem5030777 {_113520 : Type'} (P : _113520 -> Prop) (a : _113520) (h1 : term115 _113520 P a) : term115 _113520 P a.
Proof. exact (h1). Qed.
Lemma lem5030783 {_113520 : Type'} (_64644 : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term137 _113520 a s P x) : term187 _113520 a P _64644.
Proof. exact (proj1 (@lem5030762 _113520 _64644 a s P x h1)). Qed.
Lemma lem5030793 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term83 _113520 s P x) : term115 _113520 P x.
Proof. exact (proj2 (@lem5030641 _113520 s P x h1)). Qed.
Lemma lem5030805 {_113520 : Type'} (_64645 : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term137 _113520 a s P x) : term84 _113520 s P _64645.
Proof. exact (proj2 (@lem5030765 _113520 _64645 a s P x h1)). Qed.
Lemma lem5030815 {_113520 : Type'} (x : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (h1 : term155 _113520 x a s P) : term115 _113520 P x.
Proof. exact (proj2 (@lem5030645 _113520 x a s P h1)). Qed.
Lemma lem5030817 {_113520 : Type'} (x : _113520) (a : _113520) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem5030825 {_113520 : Type'} (_64647 : _113520) (x : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (h1 : term155 _113520 x a s P) : term84 _113520 s P _64647.
Proof. exact (EQ_MP (@lem5030770 _113520 s P _64647) (@lem5030769 _113520 _64647 x a s P h1)). Qed.
Lemma lem5030827 {_113520 : Type'} (x : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (h1 : term155 _113520 x a s P) : term115 _113520 P x.
Proof. exact (proj2 (@lem5030645 _113520 x a s P h1)). Qed.
Lemma lem5030829 {_113520 : Type'} (x : _113520) (s : _113520 -> Prop) (h1 : @IN _113520 x s) : @IN _113520 x s.
Proof. exact (h1). Qed.
Lemma lem5030872 {_113520 : Type'} (P : _113520 -> Prop) : (term188 _113520 P) = (term188 _113520 P).
Proof. exact (eq_refl (term188 _113520 P)). Qed.
Lemma lem5030873 {_113520 : Type'} (P : _113520 -> Prop) (x : _113520) (a : _113520) (h1 : x = a) : (term189 _113520 P x) = (term189 _113520 P a).
Proof. exact (MK_COMB (@lem5030872 _113520 P) (@lem5030817 _113520 x a h1)). Qed.
Lemma lem5030874 {_113520 : Type'} (P : _113520 -> Prop) (a : _113520) : (term189 _113520 P a) = (term115 _113520 P a).
Proof. exact (eq_refl (term189 _113520 P a)). Qed.
Lemma lem5030875 {_113520 : Type'} (P : _113520 -> Prop) (x : _113520) : (term190 _113520 P x) = (term190 _113520 P x).
Proof. exact (eq_refl (term190 _113520 P x)). Qed.
Lemma lem5030876 {_113520 : Type'} (x : _113520) (P : _113520 -> Prop) (a : _113520) : ((term189 _113520 P x) = (term189 _113520 P a)) = ((term189 _113520 P x) = (term115 _113520 P a)).
Proof. exact (MK_COMB (@lem5030875 _113520 P x) (@lem5030874 _113520 P a)). Qed.
Lemma lem5030877 {_113520 : Type'} (P : _113520 -> Prop) (x : _113520) : (term189 _113520 P x) = (term115 _113520 P x).
Proof. exact (eq_refl (term189 _113520 P x)). Qed.
Lemma lem5030878 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5030879 {_113520 : Type'} (P : _113520 -> Prop) (x : _113520) : (term190 _113520 P x) = (term191 _113520 P x).
Proof. exact (MK_COMB (@lem5030878) (@lem5030877 _113520 P x)). Qed.
Lemma lem5030880 {_113520 : Type'} (P : _113520 -> Prop) (a : _113520) : (term115 _113520 P a) = (term115 _113520 P a).
Proof. exact (eq_refl (term115 _113520 P a)). Qed.
Lemma lem5030881 {_113520 : Type'} (x : _113520) (P : _113520 -> Prop) (a : _113520) : ((term189 _113520 P x) = (term115 _113520 P a)) = ((term115 _113520 P x) = (term115 _113520 P a)).
Proof. exact (MK_COMB (@lem5030879 _113520 P x) (@lem5030880 _113520 P a)). Qed.
Lemma lem5030882 {_113520 : Type'} (x : _113520) (P : _113520 -> Prop) (a : _113520) : ((term189 _113520 P x) = (term189 _113520 P a)) = ((term115 _113520 P x) = (term115 _113520 P a)).
Proof. exact (TRANS (@lem5030876 _113520 x P a) (@lem5030881 _113520 x P a)). Qed.
Lemma lem5030883 {_113520 : Type'} (P : _113520 -> Prop) (x : _113520) (a : _113520) (h1 : x = a) : (term115 _113520 P x) = (term115 _113520 P a).
Proof. exact (EQ_MP (@lem5030882 _113520 x P a) (@lem5030873 _113520 P x a h1)). Qed.
Lemma lem5030884 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (a : _113520) (h1 : term155 _113520 x a s P) (h2 : x = a) : term115 _113520 P a.
Proof. exact (EQ_MP (@lem5030883 _113520 P x a h2) (@lem5030815 _113520 x a s P h1)). Qed.
Lemma lem5030921 {_113520 : Type'} (x : _113520) : x = x.
Proof. exact (@lem21386 _113520 x). Qed.
Lemma lem5030922 {_113520 : Type'} (x : _113520) : x = x.
Proof. exact (@lem5030921 _113520 x). Qed.
Lemma lem5030923 {_113520 : Type'} (a : _113520) : a = a.
Proof. exact (@lem5030922 _113520 a). Qed.
Lemma lem5030924 {_113520 : Type'} (a : _113520) : term192 _113520 a.
Proof. exact (fun h0 : term193 _113520 a => @lem5030923 _113520 a). Qed.
Lemma lem5030926 (p : Prop) : (term194 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5030927 {_113520 : Type'} (a : _113520) : (term192 _113520 a) = (a = a).
Proof. exact (@lem5030926 (a = a)). Qed.
Lemma lem5030928 {_113520 : Type'} (a : _113520) : a = a.
Proof. exact (EQ_MP (@lem5030927 _113520 a) (@lem5030924 _113520 a)). Qed.
Lemma lem5030934 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5030935 {_113520 : Type'} (P : _113520 -> Prop) (_64644 : _113520) (a : _113520) : (term187 _113520 a P _64644) = (term195 _113520 P _64644 a).
Proof. exact (@lem5030934 (P _64644) (term181 _113520 _64644 a)). Qed.
Lemma lem5030943 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5030944 {_113520 : Type'} (P : _113520 -> Prop) (_64644 : _113520) (a : _113520) : (term196 _113520 a P _64644) = (term197 _113520 P _64644 a).
Proof. exact (MK_COMB (@lem5030943) (@lem5030935 _113520 P _64644 a)). Qed.
Lemma lem5030952 {_113520 : Type'} (P : _113520 -> Prop) (_64644 : _113520) (a : _113520) : (term195 _113520 P _64644 a) = (term195 _113520 P _64644 a).
Proof. exact (eq_refl (term195 _113520 P _64644 a)). Qed.
Lemma lem5030953 {_113520 : Type'} (P : _113520 -> Prop) (_64644 : _113520) (a : _113520) : ((term187 _113520 a P _64644) = (term195 _113520 P _64644 a)) = ((term195 _113520 P _64644 a) = (term195 _113520 P _64644 a)).
Proof. exact (MK_COMB (@lem5030944 _113520 P _64644 a) (@lem5030952 _113520 P _64644 a)). Qed.
Lemma lem5030955 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5030956 (x : Prop) : (x = x) = True.
Proof. exact (@lem5030955 Prop x). Qed.
Lemma lem5030957 {_113520 : Type'} (P : _113520 -> Prop) (_64644 : _113520) (a : _113520) : ((term195 _113520 P _64644 a) = (term195 _113520 P _64644 a)) = True.
Proof. exact (@lem5030956 (term195 _113520 P _64644 a)). Qed.
Lemma lem5030958 {_113520 : Type'} (P : _113520 -> Prop) (_64644 : _113520) (a : _113520) : ((term187 _113520 a P _64644) = (term195 _113520 P _64644 a)) = True.
Proof. exact (TRANS (@lem5030953 _113520 P _64644 a) (@lem5030957 _113520 P _64644 a)). Qed.
Lemma lem5030959 {_113520 : Type'} (P : _113520 -> Prop) (_64644 : _113520) (a : _113520) : True = ((term187 _113520 a P _64644) = (term195 _113520 P _64644 a)).
Proof. exact (SYM (@lem5030958 _113520 P _64644 a)). Qed.
Lemma lem5030960 {_113520 : Type'} (P : _113520 -> Prop) (_64644 : _113520) (a : _113520) : (term187 _113520 a P _64644) = (term195 _113520 P _64644 a).
Proof. exact (EQ_MP (@lem5030959 _113520 P _64644 a) (@lem0)). Qed.
Lemma lem5030961 {_113520 : Type'} (_64644 : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term137 _113520 a s P x) : term195 _113520 P _64644 a.
Proof. exact (EQ_MP (@lem5030960 _113520 P _64644 a) (@lem5030783 _113520 _64644 a s P x h1)). Qed.
Lemma lem5030963 (b : Prop) (a : Prop) : (a \/ b) = (term198 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5030964 {_113520 : Type'} (a : _113520) (P : _113520 -> Prop) (_64644 : _113520) : (term195 _113520 P _64644 a) = (term199 _113520 a P _64644).
Proof. exact (@lem5030963 (term181 _113520 _64644 a) (P _64644)). Qed.
Lemma lem5030966 (a : Prop) : (term56 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5030967 {_113520 : Type'} (_64644 : _113520) (a : _113520) : (term200 _113520 _64644 a) = (_64644 = a).
Proof. exact (@lem5030966 (_64644 = a)). Qed.
Lemma lem5030968 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5030969 {_113520 : Type'} (_64644 : _113520) (a : _113520) : (term201 _113520 _64644 a) = (term202 _113520 _64644 a).
Proof. exact (MK_COMB (@lem5030968) (@lem5030967 _113520 _64644 a)). Qed.
Lemma lem5030970 {_113520 : Type'} (P : _113520 -> Prop) (_64644 : _113520) : (P _64644) = (P _64644).
Proof. exact (eq_refl (P _64644)). Qed.
Lemma lem5030971 {_113520 : Type'} (a : _113520) (P : _113520 -> Prop) (_64644 : _113520) : (term199 _113520 a P _64644) = (term203 _113520 a P _64644).
Proof. exact (MK_COMB (@lem5030969 _113520 _64644 a) (@lem5030970 _113520 P _64644)). Qed.
Lemma lem5030972 {_113520 : Type'} (a : _113520) (P : _113520 -> Prop) (_64644 : _113520) : (term195 _113520 P _64644 a) = (term203 _113520 a P _64644).
Proof. exact (TRANS (@lem5030964 _113520 a P _64644) (@lem5030971 _113520 a P _64644)). Qed.
Lemma lem5030975 {_113520 : Type'} (_64644 : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term137 _113520 a s P x) : term203 _113520 a P _64644.
Proof. exact (EQ_MP (@lem5030972 _113520 a P _64644) (@lem5030961 _113520 _64644 a s P x h1)). Qed.
Lemma lem5030976 {_113520 : Type'} (_64644 : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term137 _113520 a s P x) : term203 _113520 a P _64644.
Proof. exact (@lem5030975 _113520 _64644 a s P x h1). Qed.
Lemma lem5030977 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term137 _113520 a s P x) : term204 _113520 P a.
Proof. exact (@lem5030976 _113520 a a s P x h1). Qed.
Lemma lem5030980 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term137 _113520 a s P x) : P a.
Proof. exact (@lem5030977 _113520 a s P x h1 (@lem5030928 _113520 a)). Qed.
Lemma lem5030981 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term137 _113520 a s P x) : term205 _113520 P a.
Proof. exact (fun h0 : term115 _113520 P a => @lem5030980 _113520 a s P x h1). Qed.
Lemma lem5030983 (p : Prop) : (term194 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5030984 {_113520 : Type'} (P : _113520 -> Prop) (a : _113520) : (term205 _113520 P a) = (P a).
Proof. exact (@lem5030983 (P a)). Qed.
Lemma lem5030985 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term137 _113520 a s P x) : P a.
Proof. exact (EQ_MP (@lem5030984 _113520 P a) (@lem5030981 _113520 a s P x h1)). Qed.
Lemma lem5030988 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5030990 {_113520 : Type'} (P : _113520 -> Prop) (a : _113520) : (term115 _113520 P a) = (term206 _113520 P a).
Proof. exact (@lem5030988 (P a)). Qed.
Lemma lem5030993 {_113520 : Type'} (P : _113520 -> Prop) (a : _113520) (h1 : term115 _113520 P a) : term206 _113520 P a.
Proof. exact (EQ_MP (@lem5030990 _113520 P a) (@lem5030777 _113520 P a h1)). Qed.
Lemma lem5030996 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term115 _113520 P a) (h2 : term137 _113520 a s P x) : False.
Proof. exact (@lem5030993 _113520 P a h1 (@lem5030985 _113520 a s P x h2)). Qed.
Lemma lem5030997 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term115 _113520 P a) (h2 : term137 _113520 a s P x) : term207.
Proof. exact (fun h0 : ~ False => @lem5030996 _113520 a s P x h1 h2). Qed.
Lemma lem5030999 (p : Prop) : (term194 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5031000 : term207 = False.
Proof. exact (@lem5030999 False). Qed.
Lemma lem5031001 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term115 _113520 P a) (h2 : term137 _113520 a s P x) : False.
Proof. exact (EQ_MP (@lem5031000) (@lem5030997 _113520 a s P x h1 h2)). Qed.
Lemma lem5031038 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term83 _113520 s P x) : @IN _113520 x s.
Proof. exact (proj1 (@lem5030641 _113520 s P x h1)). Qed.
Lemma lem5031039 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term83 _113520 s P x) : term208 _113520 x s.
Proof. exact (fun h0 : term182 _113520 x s => @lem5031038 _113520 s P x h1). Qed.
Lemma lem5031041 (p : Prop) : (term194 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5031042 {_113520 : Type'} (x : _113520) (s : _113520 -> Prop) : (term208 _113520 x s) = (@IN _113520 x s).
Proof. exact (@lem5031041 (@IN _113520 x s)). Qed.
Lemma lem5031043 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term83 _113520 s P x) : @IN _113520 x s.
Proof. exact (EQ_MP (@lem5031042 _113520 x s) (@lem5031039 _113520 s P x h1)). Qed.
Lemma lem5031049 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5031050 {_113520 : Type'} (P : _113520 -> Prop) (_64645 : _113520) (s : _113520 -> Prop) : (term84 _113520 s P _64645) = (term209 _113520 P _64645 s).
Proof. exact (@lem5031049 (P _64645) (term182 _113520 _64645 s)). Qed.
Lemma lem5031056 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5031057 {_113520 : Type'} (P : _113520 -> Prop) (_64645 : _113520) (s : _113520 -> Prop) : (term210 _113520 s P _64645) = (term211 _113520 P _64645 s).
Proof. exact (MK_COMB (@lem5031056) (@lem5031050 _113520 P _64645 s)). Qed.
Lemma lem5031063 {_113520 : Type'} (P : _113520 -> Prop) (_64645 : _113520) (s : _113520 -> Prop) : (term209 _113520 P _64645 s) = (term209 _113520 P _64645 s).
Proof. exact (eq_refl (term209 _113520 P _64645 s)). Qed.
Lemma lem5031064 {_113520 : Type'} (P : _113520 -> Prop) (_64645 : _113520) (s : _113520 -> Prop) : ((term84 _113520 s P _64645) = (term209 _113520 P _64645 s)) = ((term209 _113520 P _64645 s) = (term209 _113520 P _64645 s)).
Proof. exact (MK_COMB (@lem5031057 _113520 P _64645 s) (@lem5031063 _113520 P _64645 s)). Qed.
Lemma lem5031066 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5031067 (x : Prop) : (x = x) = True.
Proof. exact (@lem5031066 Prop x). Qed.
Lemma lem5031068 {_113520 : Type'} (P : _113520 -> Prop) (_64645 : _113520) (s : _113520 -> Prop) : ((term209 _113520 P _64645 s) = (term209 _113520 P _64645 s)) = True.
Proof. exact (@lem5031067 (term209 _113520 P _64645 s)). Qed.
Lemma lem5031069 {_113520 : Type'} (P : _113520 -> Prop) (_64645 : _113520) (s : _113520 -> Prop) : ((term84 _113520 s P _64645) = (term209 _113520 P _64645 s)) = True.
Proof. exact (TRANS (@lem5031064 _113520 P _64645 s) (@lem5031068 _113520 P _64645 s)). Qed.
Lemma lem5031070 {_113520 : Type'} (P : _113520 -> Prop) (_64645 : _113520) (s : _113520 -> Prop) : True = ((term84 _113520 s P _64645) = (term209 _113520 P _64645 s)).
Proof. exact (SYM (@lem5031069 _113520 P _64645 s)). Qed.
Lemma lem5031071 {_113520 : Type'} (P : _113520 -> Prop) (_64645 : _113520) (s : _113520 -> Prop) : (term84 _113520 s P _64645) = (term209 _113520 P _64645 s).
Proof. exact (EQ_MP (@lem5031070 _113520 P _64645 s) (@lem0)). Qed.
Lemma lem5031072 {_113520 : Type'} (_64645 : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term137 _113520 a s P x) : term209 _113520 P _64645 s.
Proof. exact (EQ_MP (@lem5031071 _113520 P _64645 s) (@lem5030805 _113520 _64645 a s P x h1)). Qed.
Lemma lem5031074 (b : Prop) (a : Prop) : (a \/ b) = (term198 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5031075 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (_64645 : _113520) : (term209 _113520 P _64645 s) = (term212 _113520 s P _64645).
Proof. exact (@lem5031074 (term182 _113520 _64645 s) (P _64645)). Qed.
Lemma lem5031077 (a : Prop) : (term56 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5031078 {_113520 : Type'} (_64645 : _113520) (s : _113520 -> Prop) : (term213 _113520 _64645 s) = (@IN _113520 _64645 s).
Proof. exact (@lem5031077 (@IN _113520 _64645 s)). Qed.
Lemma lem5031079 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5031080 {_113520 : Type'} (_64645 : _113520) (s : _113520 -> Prop) : (term214 _113520 _64645 s) = (term215 _113520 _64645 s).
Proof. exact (MK_COMB (@lem5031079) (@lem5031078 _113520 _64645 s)). Qed.
Lemma lem5031081 {_113520 : Type'} (P : _113520 -> Prop) (_64645 : _113520) : (P _64645) = (P _64645).
Proof. exact (eq_refl (P _64645)). Qed.
Lemma lem5031082 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (_64645 : _113520) : (term212 _113520 s P _64645) = (term57 _113520 s P _64645).
Proof. exact (MK_COMB (@lem5031080 _113520 _64645 s) (@lem5031081 _113520 P _64645)). Qed.
Lemma lem5031083 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (_64645 : _113520) : (term209 _113520 P _64645 s) = (term57 _113520 s P _64645).
Proof. exact (TRANS (@lem5031075 _113520 s P _64645) (@lem5031082 _113520 s P _64645)). Qed.
Lemma lem5031086 {_113520 : Type'} (_64645 : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term137 _113520 a s P x) : term57 _113520 s P _64645.
Proof. exact (EQ_MP (@lem5031083 _113520 s P _64645) (@lem5031072 _113520 _64645 a s P x h1)). Qed.
Lemma lem5031087 {_113520 : Type'} (_64645 : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term137 _113520 a s P x) : term57 _113520 s P _64645.
Proof. exact (@lem5031086 _113520 _64645 a s P x h1). Qed.
Lemma lem5031088 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term137 _113520 a s P x) : term57 _113520 s P x.
Proof. exact (@lem5031087 _113520 x a s P x h1). Qed.
Lemma lem5031091 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term137 _113520 a s P x) (h2 : term83 _113520 s P x) : P x.
Proof. exact (@lem5031088 _113520 a s P x h1 (@lem5031043 _113520 s P x h2)). Qed.
Lemma lem5031092 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term137 _113520 a s P x) (h2 : term83 _113520 s P x) : term205 _113520 P x.
Proof. exact (fun h0 : term115 _113520 P x => @lem5031091 _113520 a s P x h1 h2). Qed.
Lemma lem5031094 (p : Prop) : (term194 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5031095 {_113520 : Type'} (P : _113520 -> Prop) (x : _113520) : (term205 _113520 P x) = (P x).
Proof. exact (@lem5031094 (P x)). Qed.
Lemma lem5031096 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term137 _113520 a s P x) (h2 : term83 _113520 s P x) : P x.
Proof. exact (EQ_MP (@lem5031095 _113520 P x) (@lem5031092 _113520 a s P x h1 h2)). Qed.
Lemma lem5031099 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5031101 {_113520 : Type'} (P : _113520 -> Prop) (x : _113520) : (term115 _113520 P x) = (term206 _113520 P x).
Proof. exact (@lem5031099 (P x)). Qed.
Lemma lem5031104 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term83 _113520 s P x) : term206 _113520 P x.
Proof. exact (EQ_MP (@lem5031101 _113520 P x) (@lem5030793 _113520 s P x h1)). Qed.
Lemma lem5031107 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term137 _113520 a s P x) (h2 : term83 _113520 s P x) : False.
Proof. exact (@lem5031104 _113520 s P x h2 (@lem5031096 _113520 a s P x h1 h2)). Qed.
Lemma lem5031108 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term137 _113520 a s P x) (h2 : term83 _113520 s P x) : term207.
Proof. exact (fun h0 : ~ False => @lem5031107 _113520 a s P x h1 h2). Qed.
Lemma lem5031110 (p : Prop) : (term194 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5031111 : term207 = False.
Proof. exact (@lem5031110 False). Qed.
Lemma lem5031112 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term137 _113520 a s P x) (h2 : term83 _113520 s P x) : False.
Proof. exact (EQ_MP (@lem5031111) (@lem5031108 _113520 a s P x h1 h2)). Qed.
Lemma lem5031114 {_113520 : Type'} (x : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (h1 : term155 _113520 x a s P) : P a.
Proof. exact (proj1 (@lem5030644 _113520 x a s P h1)). Qed.
Lemma lem5031115 {_113520 : Type'} (x : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (h1 : term155 _113520 x a s P) : term205 _113520 P a.
Proof. exact (fun h0 : term115 _113520 P a => @lem5031114 _113520 x a s P h1). Qed.
Lemma lem5031117 (p : Prop) : (term194 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5031118 {_113520 : Type'} (P : _113520 -> Prop) (a : _113520) : (term205 _113520 P a) = (P a).
Proof. exact (@lem5031117 (P a)). Qed.
Lemma lem5031119 {_113520 : Type'} (x : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (h1 : term155 _113520 x a s P) : P a.
Proof. exact (EQ_MP (@lem5031118 _113520 P a) (@lem5031115 _113520 x a s P h1)). Qed.
Lemma lem5031122 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5031124 {_113520 : Type'} (P : _113520 -> Prop) (a : _113520) : (term115 _113520 P a) = (term206 _113520 P a).
Proof. exact (@lem5031122 (P a)). Qed.
Lemma lem5031127 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (a : _113520) (h1 : term155 _113520 x a s P) (h2 : x = a) : term206 _113520 P a.
Proof. exact (EQ_MP (@lem5031124 _113520 P a) (@lem5030884 _113520 s P x a h1 h2)). Qed.
Lemma lem5031130 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (a : _113520) (h1 : term155 _113520 x a s P) (h2 : x = a) : False.
Proof. exact (@lem5031127 _113520 s P x a h1 h2 (@lem5031119 _113520 x a s P h1)). Qed.
Lemma lem5031131 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (a : _113520) (h1 : term155 _113520 x a s P) (h2 : x = a) : term207.
Proof. exact (fun h0 : ~ False => @lem5031130 _113520 s P x a h1 h2). Qed.
Lemma lem5031133 (p : Prop) : (term194 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5031134 : term207 = False.
Proof. exact (@lem5031133 False). Qed.
Lemma lem5031137 {_113520 : Type'} (x : _113520) (s : _113520 -> Prop) (h1 : @IN _113520 x s) : @IN _113520 x s.
Proof. exact (h1). Qed.
Lemma lem5031138 {_113520 : Type'} (x : _113520) (s : _113520 -> Prop) (h1 : @IN _113520 x s) : term208 _113520 x s.
Proof. exact (fun h0 : term182 _113520 x s => @lem5031137 _113520 x s h1). Qed.
Lemma lem5031140 (p : Prop) : (term194 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5031141 {_113520 : Type'} (x : _113520) (s : _113520 -> Prop) : (term208 _113520 x s) = (@IN _113520 x s).
Proof. exact (@lem5031140 (@IN _113520 x s)). Qed.
Lemma lem5031142 {_113520 : Type'} (x : _113520) (s : _113520 -> Prop) (h1 : @IN _113520 x s) : @IN _113520 x s.
Proof. exact (EQ_MP (@lem5031141 _113520 x s) (@lem5031138 _113520 x s h1)). Qed.
Lemma lem5031148 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5031149 {_113520 : Type'} (P : _113520 -> Prop) (_64647 : _113520) (s : _113520 -> Prop) : (term84 _113520 s P _64647) = (term209 _113520 P _64647 s).
Proof. exact (@lem5031148 (P _64647) (term182 _113520 _64647 s)). Qed.
Lemma lem5031155 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5031156 {_113520 : Type'} (P : _113520 -> Prop) (_64647 : _113520) (s : _113520 -> Prop) : (term210 _113520 s P _64647) = (term211 _113520 P _64647 s).
Proof. exact (MK_COMB (@lem5031155) (@lem5031149 _113520 P _64647 s)). Qed.
Lemma lem5031162 {_113520 : Type'} (P : _113520 -> Prop) (_64647 : _113520) (s : _113520 -> Prop) : (term209 _113520 P _64647 s) = (term209 _113520 P _64647 s).
Proof. exact (eq_refl (term209 _113520 P _64647 s)). Qed.
Lemma lem5031163 {_113520 : Type'} (P : _113520 -> Prop) (_64647 : _113520) (s : _113520 -> Prop) : ((term84 _113520 s P _64647) = (term209 _113520 P _64647 s)) = ((term209 _113520 P _64647 s) = (term209 _113520 P _64647 s)).
Proof. exact (MK_COMB (@lem5031156 _113520 P _64647 s) (@lem5031162 _113520 P _64647 s)). Qed.
Lemma lem5031165 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5031166 (x : Prop) : (x = x) = True.
Proof. exact (@lem5031165 Prop x). Qed.
Lemma lem5031167 {_113520 : Type'} (P : _113520 -> Prop) (_64647 : _113520) (s : _113520 -> Prop) : ((term209 _113520 P _64647 s) = (term209 _113520 P _64647 s)) = True.
Proof. exact (@lem5031166 (term209 _113520 P _64647 s)). Qed.
Lemma lem5031168 {_113520 : Type'} (P : _113520 -> Prop) (_64647 : _113520) (s : _113520 -> Prop) : ((term84 _113520 s P _64647) = (term209 _113520 P _64647 s)) = True.
Proof. exact (TRANS (@lem5031163 _113520 P _64647 s) (@lem5031167 _113520 P _64647 s)). Qed.
Lemma lem5031169 {_113520 : Type'} (P : _113520 -> Prop) (_64647 : _113520) (s : _113520 -> Prop) : True = ((term84 _113520 s P _64647) = (term209 _113520 P _64647 s)).
Proof. exact (SYM (@lem5031168 _113520 P _64647 s)). Qed.
Lemma lem5031170 {_113520 : Type'} (P : _113520 -> Prop) (_64647 : _113520) (s : _113520 -> Prop) : (term84 _113520 s P _64647) = (term209 _113520 P _64647 s).
Proof. exact (EQ_MP (@lem5031169 _113520 P _64647 s) (@lem0)). Qed.
Lemma lem5031171 {_113520 : Type'} (_64647 : _113520) (x : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (h1 : term155 _113520 x a s P) : term209 _113520 P _64647 s.
Proof. exact (EQ_MP (@lem5031170 _113520 P _64647 s) (@lem5030825 _113520 _64647 x a s P h1)). Qed.
Lemma lem5031173 (b : Prop) (a : Prop) : (a \/ b) = (term198 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5031174 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (_64647 : _113520) : (term209 _113520 P _64647 s) = (term212 _113520 s P _64647).
Proof. exact (@lem5031173 (term182 _113520 _64647 s) (P _64647)). Qed.
Lemma lem5031176 (a : Prop) : (term56 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5031177 {_113520 : Type'} (_64647 : _113520) (s : _113520 -> Prop) : (term213 _113520 _64647 s) = (@IN _113520 _64647 s).
Proof. exact (@lem5031176 (@IN _113520 _64647 s)). Qed.
Lemma lem5031178 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5031179 {_113520 : Type'} (_64647 : _113520) (s : _113520 -> Prop) : (term214 _113520 _64647 s) = (term215 _113520 _64647 s).
Proof. exact (MK_COMB (@lem5031178) (@lem5031177 _113520 _64647 s)). Qed.
Lemma lem5031180 {_113520 : Type'} (P : _113520 -> Prop) (_64647 : _113520) : (P _64647) = (P _64647).
Proof. exact (eq_refl (P _64647)). Qed.
Lemma lem5031181 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (_64647 : _113520) : (term212 _113520 s P _64647) = (term57 _113520 s P _64647).
Proof. exact (MK_COMB (@lem5031179 _113520 _64647 s) (@lem5031180 _113520 P _64647)). Qed.
Lemma lem5031182 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (_64647 : _113520) : (term209 _113520 P _64647 s) = (term57 _113520 s P _64647).
Proof. exact (TRANS (@lem5031174 _113520 s P _64647) (@lem5031181 _113520 s P _64647)). Qed.
Lemma lem5031185 {_113520 : Type'} (_64647 : _113520) (x : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (h1 : term155 _113520 x a s P) : term57 _113520 s P _64647.
Proof. exact (EQ_MP (@lem5031182 _113520 s P _64647) (@lem5031171 _113520 _64647 x a s P h1)). Qed.
Lemma lem5031186 {_113520 : Type'} (_64647 : _113520) (x : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (h1 : term155 _113520 x a s P) : term57 _113520 s P _64647.
Proof. exact (@lem5031185 _113520 _64647 x a s P h1). Qed.
Lemma lem5031187 {_113520 : Type'} (x : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (h1 : term155 _113520 x a s P) : term57 _113520 s P x.
Proof. exact (@lem5031186 _113520 x x a s P h1). Qed.
Lemma lem5031190 {_113520 : Type'} (a : _113520) (P : _113520 -> Prop) (x : _113520) (s : _113520 -> Prop) (h1 : term155 _113520 x a s P) (h2 : @IN _113520 x s) : P x.
Proof. exact (@lem5031187 _113520 x a s P h1 (@lem5031142 _113520 x s h2)). Qed.
Lemma lem5031191 {_113520 : Type'} (a : _113520) (P : _113520 -> Prop) (x : _113520) (s : _113520 -> Prop) (h1 : term155 _113520 x a s P) (h2 : @IN _113520 x s) : term205 _113520 P x.
Proof. exact (fun h0 : term115 _113520 P x => @lem5031190 _113520 a P x s h1 h2). Qed.
Lemma lem5031193 (p : Prop) : (term194 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5031194 {_113520 : Type'} (P : _113520 -> Prop) (x : _113520) : (term205 _113520 P x) = (P x).
Proof. exact (@lem5031193 (P x)). Qed.
Lemma lem5031195 {_113520 : Type'} (a : _113520) (P : _113520 -> Prop) (x : _113520) (s : _113520 -> Prop) (h1 : term155 _113520 x a s P) (h2 : @IN _113520 x s) : P x.
Proof. exact (EQ_MP (@lem5031194 _113520 P x) (@lem5031191 _113520 a P x s h1 h2)). Qed.
Lemma lem5031198 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5031200 {_113520 : Type'} (P : _113520 -> Prop) (x : _113520) : (term115 _113520 P x) = (term206 _113520 P x).
Proof. exact (@lem5031198 (P x)). Qed.
Lemma lem5031203 {_113520 : Type'} (x : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (h1 : term155 _113520 x a s P) : term206 _113520 P x.
Proof. exact (EQ_MP (@lem5031200 _113520 P x) (@lem5030827 _113520 x a s P h1)). Qed.
Lemma lem5031206 {_113520 : Type'} (a : _113520) (P : _113520 -> Prop) (x : _113520) (s : _113520 -> Prop) (h1 : term155 _113520 x a s P) (h2 : @IN _113520 x s) : False.
Proof. exact (@lem5031203 _113520 x a s P h1 (@lem5031195 _113520 a P x s h1 h2)). Qed.
Lemma lem5031207 {_113520 : Type'} (a : _113520) (P : _113520 -> Prop) (x : _113520) (s : _113520 -> Prop) (h1 : term155 _113520 x a s P) (h2 : @IN _113520 x s) : term207.
Proof. exact (fun h0 : ~ False => @lem5031206 _113520 a P x s h1 h2). Qed.
Lemma lem5031209 (p : Prop) : (term194 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5031210 : term207 = False.
Proof. exact (@lem5031209 False). Qed.
Lemma lem5031211 {_113520 : Type'} (a : _113520) (P : _113520 -> Prop) (x : _113520) (s : _113520 -> Prop) (h1 : term155 _113520 x a s P) (h2 : @IN _113520 x s) : False.
Proof. exact (EQ_MP (@lem5031210) (@lem5031207 _113520 a P x s h1 h2)). Qed.
Lemma lem5031212 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (a : _113520) (h1 : term155 _113520 x a s P) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem5031134) (@lem5031131 _113520 s P x a h1 h2)). Qed.
Lemma lem5031213 {_113520 : Type'} (a : _113520) (P : _113520 -> Prop) (x : _113520) (s : _113520 -> Prop) (h1 : term155 _113520 x a s P) (h2 : @IN _113520 x s) : (@IN _113520 x s) = False.
Proof. exact (prop_ext (fun h3 : @IN _113520 x s => @lem5031211 _113520 a P x s h1 h2) (fun h3 : False => @lem5030829 _113520 x s h2)). Qed.
Lemma lem5031214 {_113520 : Type'} (a : _113520) (P : _113520 -> Prop) (x : _113520) (s : _113520 -> Prop) (h1 : term155 _113520 x a s P) (h2 : @IN _113520 x s) : False.
Proof. exact (EQ_MP (@lem5031213 _113520 a P x s h1 h2) (@lem5030829 _113520 x s h2)). Qed.
Lemma lem5031215 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (a : _113520) (h1 : term155 _113520 x a s P) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem5031212 _113520 s P x a h1 h2) (fun h3 : False => @lem5030817 _113520 x a h2)). Qed.
Lemma lem5031216 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (a : _113520) (h1 : term155 _113520 x a s P) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem5031215 _113520 s P x a h1 h2) (@lem5030817 _113520 x a h2)). Qed.
Lemma lem5031217 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term115 _113520 P a) (h2 : term137 _113520 a s P x) : (term115 _113520 P a) = False.
Proof. exact (prop_ext (fun h3 : term115 _113520 P a => @lem5031001 _113520 a s P x h1 h2) (fun h3 : False => @lem5030777 _113520 P a h1)). Qed.
Lemma lem5031218 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term115 _113520 P a) (h2 : term137 _113520 a s P x) : False.
Proof. exact (EQ_MP (@lem5031217 _113520 a s P x h1 h2) (@lem5030777 _113520 P a h1)). Qed.
Lemma lem5031219 {_113520 : Type'} (a : _113520) (P : _113520 -> Prop) (x : _113520) (s : _113520 -> Prop) (h1 : term155 _113520 x a s P) (h2 : @IN _113520 x s) : (@IN _113520 x s) = False.
Proof. exact (prop_ext (fun h3 : @IN _113520 x s => @lem5031214 _113520 a P x s h1 h2) (fun h3 : False => @lem5030759 _113520 x s h2)). Qed.
Lemma lem5031220 {_113520 : Type'} (a : _113520) (P : _113520 -> Prop) (x : _113520) (s : _113520 -> Prop) (h1 : term155 _113520 x a s P) (h2 : @IN _113520 x s) : False.
Proof. exact (EQ_MP (@lem5031219 _113520 a P x s h1 h2) (@lem5030759 _113520 x s h2)). Qed.
Lemma lem5031221 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (a : _113520) (h1 : term155 _113520 x a s P) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem5031216 _113520 s P x a h1 h2) (fun h3 : False => @lem5030734 _113520 x a h2)). Qed.
Lemma lem5031222 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (a : _113520) (h1 : term155 _113520 x a s P) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem5031221 _113520 s P x a h1 h2) (@lem5030734 _113520 x a h2)). Qed.
Lemma lem5031223 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term115 _113520 P a) (h2 : term137 _113520 a s P x) : (term115 _113520 P a) = False.
Proof. exact (prop_ext (fun h3 : term115 _113520 P a => @lem5031218 _113520 a s P x h1 h2) (fun h3 : False => @lem5030678 _113520 P a h1)). Qed.
Lemma lem5031224 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term115 _113520 P a) (h2 : term137 _113520 a s P x) : False.
Proof. exact (EQ_MP (@lem5031223 _113520 a s P x h1 h2) (@lem5030678 _113520 P a h1)). Qed.
Lemma lem5031225 {_113520 : Type'} (a : _113520) (P : _113520 -> Prop) (x : _113520) (s : _113520 -> Prop) (h1 : term155 _113520 x a s P) (h2 : @IN _113520 x s) : (@IN _113520 x s) = False.
Proof. exact (prop_ext (fun h3 : @IN _113520 x s => @lem5031220 _113520 a P x s h1 h2) (fun h3 : False => @lem5030759 _113520 x s h2)). Qed.
Lemma lem5031226 {_113520 : Type'} (a : _113520) (P : _113520 -> Prop) (x : _113520) (s : _113520 -> Prop) (h1 : term155 _113520 x a s P) (h2 : @IN _113520 x s) : False.
Proof. exact (EQ_MP (@lem5031225 _113520 a P x s h1 h2) (@lem5030759 _113520 x s h2)). Qed.
Lemma lem5031227 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (a : _113520) (h1 : term155 _113520 x a s P) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem5031222 _113520 s P x a h1 h2) (fun h3 : False => @lem5030734 _113520 x a h2)). Qed.
Lemma lem5031228 {_113520 : Type'} (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (a : _113520) (h1 : term155 _113520 x a s P) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem5031227 _113520 s P x a h1 h2) (@lem5030734 _113520 x a h2)). Qed.
Lemma lem5031229 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term115 _113520 P a) (h2 : term137 _113520 a s P x) : (term115 _113520 P a) = False.
Proof. exact (prop_ext (fun h3 : term115 _113520 P a => @lem5031224 _113520 a s P x h1 h2) (fun h3 : False => @lem5030678 _113520 P a h1)). Qed.
Lemma lem5031230 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term115 _113520 P a) (h2 : term137 _113520 a s P x) : False.
Proof. exact (EQ_MP (@lem5031229 _113520 a s P x h1 h2) (@lem5030678 _113520 P a h1)). Qed.
Lemma lem5031231 {_113520 : Type'} (x : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (h1 : term155 _113520 x a s P) : False.
Proof. exact (or_elim (@lem5030649 _113520 x a s P h1) (fun h0 : x = a => @lem5031228 _113520 s P x a h1 h0) (fun h0 : @IN _113520 x s => @lem5031226 _113520 a P x s h1 h0)). Qed.
Lemma lem5031232 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (x : _113520) (h1 : term137 _113520 a s P x) : False.
Proof. exact (or_elim (@lem5030638 _113520 a s P x h1) (fun h0 : term115 _113520 P a => @lem5031230 _113520 a s P x h0 h1) (fun h0 : term83 _113520 s P x => @lem5031112 _113520 a s P x h1 h0)). Qed.
Lemma lem5031233 {_113520 : Type'} (x : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (h1 : term176 _113520 x a s P) : False.
Proof. exact (or_elim (@lem5030635 _113520 x a s P h1) (fun h0 : term137 _113520 a s P x => @lem5031232 _113520 a s P x h0) (fun h0 : term155 _113520 x a s P => @lem5031231 _113520 x a s P h0)). Qed.
Lemma lem5031234 {_113520 : Type'} (x : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (h1 : term176 _113520 x a s P) : (term176 _113520 x a s P) = False.
Proof. exact (prop_ext (fun h2 : term176 _113520 x a s P => @lem5031233 _113520 x a s P h1) (fun h2 : False => @lem5030635 _113520 x a s P h1)). Qed.
Lemma lem5031235 {_113520 : Type'} (x : _113520) (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (h1 : term176 _113520 x a s P) : False.
Proof. exact (EQ_MP (@lem5031234 _113520 x a s P h1) (@lem5030635 _113520 x a s P h1)). Qed.
Lemma lem5031236 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (h1 : term62 _113520 a s P) : False.
Proof. exact (ex_elim (@lem5030534 _113520 a s P h1) (fun x : _113520 => fun h0 : term178 _113520 a s P x => @lem5031235 _113520 x a s P h0)). Qed.
Lemma lem5031237 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (h1 : term62 _113520 a s P) : (term62 _113520 a s P) = False.
Proof. exact (prop_ext (fun h2 : term62 _113520 a s P => @lem5031236 _113520 a s P h1) (fun h2 : False => @lem5030187 _113520 a s P h1)). Qed.
Lemma lem5031238 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) (h1 : term62 _113520 a s P) : False.
Proof. exact (EQ_MP (@lem5031237 _113520 a s P h1) (@lem5030187 _113520 a s P h1)). Qed.
Lemma lem5031239 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : term61 _113520 a s P.
Proof. exact (fun h0 : term62 _113520 a s P => @lem5031238 _113520 a s P h0). Qed.
Lemma lem5031240 {_113520 : Type'} (a : _113520) (s : _113520 -> Prop) (P : _113520 -> Prop) : (term31 _113520 a s P) = (term34 _113520 a s P).
Proof. exact (EQ_MP (@lem5030186 _113520 a s P) (@lem5031239 _113520 a s P)). Qed.
Lemma lem5031245 {_113520 : Type'} (a : _113520) (P : _113520 -> Prop) : term38 _113520 a P.
Proof. exact (fun s : _113520 -> Prop => @lem5031240 _113520 a s P). Qed.
Lemma lem5031250 {_113520 : Type'} (P : _113520 -> Prop) : term42 _113520 P.
Proof. exact (fun a : _113520 => @lem5031245 _113520 a P). Qed.
Lemma lem5031255 {_113520 : Type'} : term46 _113520.
Proof. exact (fun P : _113520 -> Prop => @lem5031250 _113520 P). Qed.
Lemma lem5031256 {_113520 : Type'} : term50 _113520.
Proof. exact (EQ_MP (@lem5030182 _113520) (@lem5031255 _113520)). Qed.
Lemma lem5031258 {_113520 : Type'} : term50 _113520.
Proof. exact (@lem5030065 _113520 (@lem5031256 _113520)). Qed.
Lemma lem5031259 {_113520 : Type'} (h1 : term51 _113520) : False.
Proof. exact (@lem5031258 _113520 (@lem5030049 _113520 h1)). Qed.
Lemma lem5031260 {_113520 : Type'} (h1 : term51 _113520) : (term51 _113520) = False.
Proof. exact (prop_ext (fun h2 : term51 _113520 => @lem5031259 _113520 h1) (fun h2 : False => @lem5030049 _113520 h1)). Qed.
Lemma lem5031261 {_113520 : Type'} (h1 : term51 _113520) : False.
Proof. exact (EQ_MP (@lem5031260 _113520 h1) (@lem5030049 _113520 h1)). Qed.
Lemma lem5031262 {_113520 : Type'} : term50 _113520.
Proof. exact (fun h0 : term51 _113520 => @lem5031261 _113520 h0). Qed.
Lemma lem5031263 {_113520 : Type'} : term46 _113520.
Proof. exact (EQ_MP (@lem5030048 _113520) (@lem5031262 _113520)). Qed.
Lemma lem5031264 {_113480 _113520 : Type'} : term47 _113480 _113520.
Proof. exact (EQ_MP (@lem5030044 _113480 _113520) (@lem5031263 _113520)). Qed.
