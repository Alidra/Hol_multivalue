Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_SWAP_term_abbrevs.
Require Import ETA_AX_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import NSUM_0_spec.
Require Import NSUM_ADD_spec.
Require Import NSUM_CLAUSES_spec.
Require Import RIGHT_FORALL_IMP_THM_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem6960935 {A B : Type'} (t : A -> B) : term0 A B t.
Proof. exact (@lem9121 A B t). Qed.
Lemma lem6960936 {A B : Type'} (t : A -> B) : (term0 A B t) = ((term1 A B t) = t).
Proof. exact (eq_refl (term0 A B t)). Qed.
Lemma lem6960937 {A B : Type'} (t : A -> B) : (term1 A B t) = t.
Proof. exact (EQ_MP (@lem6960936 A B t) (@lem6960935 A B t)). Qed.
Lemma lem6960938 {_126729 : Type'} (f : _126729 -> nat) : term2 _126729 f.
Proof. exact (@lem6930477 _126729 f). Qed.
Lemma lem6960939 {_126729 : Type'} (f : _126729 -> nat) : (term2 _126729 f) = (term3 _126729 f).
Proof. exact (eq_refl (term2 _126729 f)). Qed.
Lemma lem6960940 {_126729 : Type'} (f : _126729 -> nat) : term3 _126729 f.
Proof. exact (EQ_MP (@lem6960939 _126729 f) (@lem6960938 _126729 f)). Qed.
Lemma lem6960941 {_126729 : Type'} (f : _126729 -> nat) (g : _126729 -> nat) : term4 _126729 f g.
Proof. exact (@lem6960940 _126729 f g). Qed.
Lemma lem6960942 {_126729 : Type'} (f : _126729 -> nat) (g : _126729 -> nat) : (term4 _126729 f g) = (term5 _126729 f g).
Proof. exact (eq_refl (term4 _126729 f g)). Qed.
Lemma lem6960943 {_126729 : Type'} (f : _126729 -> nat) (g : _126729 -> nat) : term5 _126729 f g.
Proof. exact (EQ_MP (@lem6960942 _126729 f g) (@lem6960941 _126729 f g)). Qed.
Lemma lem6960944 {_126729 : Type'} (f : _126729 -> nat) (g : _126729 -> nat) (s : _126729 -> Prop) : term6 _126729 f g s.
Proof. exact (@lem6960943 _126729 f g s). Qed.
Lemma lem6960945 {_126729 : Type'} (f : _126729 -> nat) (s : _126729 -> Prop) (g : _126729 -> nat) : (term6 _126729 f g s) = (term7 _126729 f s g).
Proof. exact (eq_refl (term6 _126729 f g s)). Qed.
Lemma lem6960946 {_126729 : Type'} (f : _126729 -> nat) (s : _126729 -> Prop) (g : _126729 -> nat) : term7 _126729 f s g.
Proof. exact (EQ_MP (@lem6960945 _126729 f s g) (@lem6960944 _126729 f g s)). Qed.
Lemma lem6960947 {_126729 : Type'} (s : _126729 -> Prop) (h1 : @FINITE _126729 s) : @FINITE _126729 s.
Proof. exact (h1). Qed.
Lemma lem6960948 {_126729 : Type'} (f : _126729 -> nat) (g : _126729 -> nat) (s : _126729 -> Prop) (h1 : @FINITE _126729 s) : (term8 _126729 s f g) = (term9 _126729 f s g).
Proof. exact (@lem6960946 _126729 f s g (@lem6960947 _126729 s h1)). Qed.
Lemma lem6960954 {A : Type'} (s : A -> Prop) : term10 A s.
Proof. exact (@lem6931080 A s). Qed.
Lemma lem6960955 {A : Type'} (s : A -> Prop) : (term10 A s) = ((term11 A s) = (NUMERAL 0)).
Proof. exact (eq_refl (term10 A s)). Qed.
Lemma lem6960957 {_126525 : Type'} : term12 _126525.
Proof. exact (proj2 (@lem6924916 Prop _126525)). Qed.
Lemma lem6960958 {_126525 : Type'} (x : _126525) : term13 _126525 x.
Proof. exact (@lem6960957 _126525 x). Qed.
Lemma lem6960959 {_126525 : Type'} (x : _126525) : (term13 _126525 x) = (term14 _126525 x).
Proof. exact (eq_refl (term13 _126525 x)). Qed.
Lemma lem6960960 {_126525 : Type'} (x : _126525) : term14 _126525 x.
Proof. exact (EQ_MP (@lem6960959 _126525 x) (@lem6960958 _126525 x)). Qed.
Lemma lem6960961 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : term15 _126525 x f.
Proof. exact (@lem6960960 _126525 x f). Qed.
Lemma lem6960962 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : (term15 _126525 x f) = (term16 _126525 x f).
Proof. exact (eq_refl (term15 _126525 x f)). Qed.
Lemma lem6960963 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : term16 _126525 x f.
Proof. exact (EQ_MP (@lem6960962 _126525 x f) (@lem6960961 _126525 x f)). Qed.
Lemma lem6960964 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) (s : _126525 -> Prop) : term17 _126525 x f s.
Proof. exact (@lem6960963 _126525 x f s). Qed.
Lemma lem6960965 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : (term17 _126525 x f s) = (term18 _126525 x s f).
Proof. exact (eq_refl (term17 _126525 x f s)). Qed.
Lemma lem6960966 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : term18 _126525 x s f.
Proof. exact (EQ_MP (@lem6960965 _126525 x s f) (@lem6960964 _126525 x f s)). Qed.
Lemma lem6960967 {_126525 : Type'} (s : _126525 -> Prop) (h1 : @FINITE _126525 s) : @FINITE _126525 s.
Proof. exact (h1). Qed.
Lemma lem6960968 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) (s : _126525 -> Prop) (h1 : @FINITE _126525 s) : (term19 _126525 x s f) = (term20 _126525 x s f).
Proof. exact (@lem6960966 _126525 x s f (@lem6960967 _126525 s h1)). Qed.
Lemma lem6960974 {_126486 : Type'} : term21 _126486.
Proof. exact (proj1 (@lem6924916 _126486 Prop)). Qed.
Lemma lem6960975 {_126486 : Type'} (f : _126486 -> nat) : term22 _126486 f.
Proof. exact (@lem6960974 _126486 f). Qed.
Lemma lem6960976 {_126486 : Type'} (f : _126486 -> nat) : (term22 _126486 f) = ((@nsum _126486 (@EMPTY _126486) f) = (NUMERAL 0)).
Proof. exact (eq_refl (term22 _126486 f)). Qed.
Lemma lem6960978 {A : Type'} (h1 : term23 A) : term23 A.
Proof. exact (h1). Qed.
Lemma lem6960979 {A : Type'} (P : type686 A) (h1 : term23 A) : term24 A P.
Proof. exact (@lem6960978 A h1 P). Qed.
Lemma lem6960980 {A : Type'} (P : type686 A) : (term24 A P) = (term25 A P).
Proof. exact (eq_refl (term24 A P)). Qed.
Lemma lem6960981 {A : Type'} (P : type686 A) (h1 : term23 A) : term25 A P.
Proof. exact (EQ_MP (@lem6960980 A P) (@lem6960979 A P h1)). Qed.
Lemma lem6960982 {A : Type'} (P : type686 A) (h1 : term26 A P) : term26 A P.
Proof. exact (h1). Qed.
Lemma lem6960983 {A : Type'} (P : type686 A) (h1 : term23 A) (h2 : term26 A P) : term27 A P.
Proof. exact (@lem6960981 A P h1 (@lem6960982 A P h2)). Qed.
Lemma lem6960984 {A : Type'} (P : type686 A) (h1 : term26 A P) : term28 A P.
Proof. exact (fun h0 : term23 A => @lem6960983 A P h0 h1). Qed.
Lemma lem6960985 {A : Type'} (h1 : term23 A) : term23 A.
Proof. exact (h1). Qed.
Lemma lem6960986 {A : Type'} (P : type686 A) (h1 : term23 A) (h2 : term26 A P) : term27 A P.
Proof. exact (@lem6960984 A P h2 (@lem6960985 A h1)). Qed.
Lemma lem6960987 {A : Type'} (P : type686 A) (h1 : term23 A) : term25 A P.
Proof. exact (fun h0 : term26 A P => @lem6960986 A P h1 h0). Qed.
Lemma lem6960988 {A : Type'} (h1 : term23 A) : term23 A.
Proof. exact (fun P : type686 A => @lem6960987 A P h1). Qed.
Lemma lem6960989 {A : Type'} : term29 A.
Proof. exact (fun h0 : term23 A => @lem6960988 A h0). Qed.
Lemma lem6960990 {A : Type'} : term23 A.
Proof. exact (@lem6960989 A (@lem3558722 A)). Qed.
Lemma lem6960991 {A : Type'} (P : type686 A) : term24 A P.
Proof. exact (@lem6960990 A P). Qed.
Lemma lem6960992 {A : Type'} (P : type686 A) : (term24 A P) = (term25 A P).
Proof. exact (eq_refl (term24 A P)). Qed.
Lemma lem6960994 {A : Type'} (P : Prop) : term30 A P.
Proof. exact (@lem6534 A P). Qed.
Lemma lem6960995 {A : Type'} (P : Prop) : (term30 A P) = (term31 A P).
Proof. exact (eq_refl (term30 A P)). Qed.
Lemma lem6960996 {A : Type'} (P : Prop) : term31 A P.
Proof. exact (EQ_MP (@lem6960995 A P) (@lem6960994 A P)). Qed.
Lemma lem6960997 {A : Type'} (P : Prop) (Q : A -> Prop) : term32 A P Q.
Proof. exact (@lem6960996 A P Q). Qed.
Lemma lem6960998 {A : Type'} (P : Prop) (Q : A -> Prop) : (term32 A P Q) = ((term33 A P Q) = (term34 A P Q)).
Proof. exact (eq_refl (term32 A P Q)). Qed.
Lemma lem6961029 (p : Prop) (q : Prop) (r : Prop) : (term35 p q r) = (term36 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem6961030 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : type1415 A B) : (term37 A B t s f) = (term38 A B t s f).
Proof. exact (@lem6961029 (@FINITE A s) (@FINITE B t) ((term39 A B s t f) = (term40 A B t s f))). Qed.
Lemma lem6961037 {A B : Type'} (s : A -> Prop) (f : type1415 A B) : (term41 A B s f) = (term42 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem6961030 A B t s f)). Qed.
Lemma lem6961038 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem6961039 {A B : Type'} (s : A -> Prop) (f : type1415 A B) : (term43 A B s f) = (term44 A B s f).
Proof. exact (MK_COMB (@lem6961038 B) (@lem6961037 A B s f)). Qed.
Lemma lem6961041 {A : Type'} (P : Prop) (Q : A -> Prop) : (term33 A P Q) = (term34 A P Q).
Proof. exact (EQ_MP (@lem6960998 A P Q) (@lem6960997 A P Q)). Qed.
Lemma lem6961042 {B : Type'} (P : Prop) (Q : type686 B) : (term45 B P Q) = (term46 B P Q).
Proof. exact (@lem6961041 (B -> Prop) P Q). Qed.
Lemma lem6961043 {A B : Type'} (s : A -> Prop) (f : type1415 A B) : (term47 A B s f) = (term48 A B s f).
Proof. exact (@lem6961042 B (@FINITE A s) (term49 A B s f)). Qed.
Lemma lem6961044 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : type1415 A B) : (term50 A B s f t) = (term51 A B t s f).
Proof. exact (eq_refl (term50 A B s f t)). Qed.
Lemma lem6961045 {A : Type'} (s : A -> Prop) : (term52 A s) = (term52 A s).
Proof. exact (eq_refl (term52 A s)). Qed.
Lemma lem6961046 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : type1415 A B) : (term53 A B s f t) = (term38 A B t s f).
Proof. exact (MK_COMB (@lem6961045 A s) (@lem6961044 A B t s f)). Qed.
Lemma lem6961047 {A B : Type'} (s : A -> Prop) (f : type1415 A B) : (term54 A B s f) = (term42 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem6961046 A B t s f)). Qed.
Lemma lem6961048 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem6961049 {A B : Type'} (s : A -> Prop) (f : type1415 A B) : (term47 A B s f) = (term44 A B s f).
Proof. exact (MK_COMB (@lem6961048 B) (@lem6961047 A B s f)). Qed.
Lemma lem6961050 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6961051 {A B : Type'} (s : A -> Prop) (f : type1415 A B) : (term55 A B s f) = (term56 A B s f).
Proof. exact (MK_COMB (@lem6961050) (@lem6961049 A B s f)). Qed.
Lemma lem6961052 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : type1415 A B) : (term50 A B s f t) = (term51 A B t s f).
Proof. exact (eq_refl (term50 A B s f t)). Qed.
Lemma lem6961053 {A B : Type'} (s : A -> Prop) (f : type1415 A B) : (term57 A B s f) = (term49 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem6961052 A B t s f)). Qed.
Lemma lem6961054 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem6961055 {A B : Type'} (s : A -> Prop) (f : type1415 A B) : (term58 A B s f) = (term59 A B s f).
Proof. exact (MK_COMB (@lem6961054 B) (@lem6961053 A B s f)). Qed.
Lemma lem6961056 {A : Type'} (s : A -> Prop) : (term52 A s) = (term52 A s).
Proof. exact (eq_refl (term52 A s)). Qed.
Lemma lem6961057 {A B : Type'} (s : A -> Prop) (f : type1415 A B) : (term48 A B s f) = (term60 A B s f).
Proof. exact (MK_COMB (@lem6961056 A s) (@lem6961055 A B s f)). Qed.
Lemma lem6961058 {A B : Type'} (s : A -> Prop) (f : type1415 A B) : ((term47 A B s f) = (term48 A B s f)) = ((term44 A B s f) = (term60 A B s f)).
Proof. exact (MK_COMB (@lem6961051 A B s f) (@lem6961057 A B s f)). Qed.
Lemma lem6961059 {A B : Type'} (s : A -> Prop) (f : type1415 A B) : (term44 A B s f) = (term60 A B s f).
Proof. exact (EQ_MP (@lem6961058 A B s f) (@lem6961043 A B s f)). Qed.
Lemma lem6961090 {A B : Type'} (s : A -> Prop) (f : type1415 A B) : (term43 A B s f) = (term60 A B s f).
Proof. exact (TRANS (@lem6961039 A B s f) (@lem6961059 A B s f)). Qed.
Lemma lem6961091 {A B : Type'} (f : type1415 A B) : (term61 A B f) = (term62 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6961090 A B s f)). Qed.
Lemma lem6961092 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6961093 {A B : Type'} (f : type1415 A B) : (term63 A B f) = (term64 A B f).
Proof. exact (MK_COMB (@lem6961092 A) (@lem6961091 A B f)). Qed.
Lemma lem6961118 {A B : Type'} (f : type1415 A B) : (term64 A B f) = (term63 A B f).
Proof. exact (SYM (@lem6961093 A B f)). Qed.
Lemma lem6961120 {A : Type'} (P : type686 A) : term25 A P.
Proof. exact (EQ_MP (@lem6960992 A P) (@lem6960991 A P)). Qed.
Lemma lem6961121 {A : Type'} (P : type686 A) : term25 A P.
Proof. exact (@lem6961120 A P). Qed.
Lemma lem6961122 {A B : Type'} (f : type1415 A B) : term65 A B f.
Proof. exact (@lem6961121 A (term66 A B f)). Qed.
Lemma lem6961123 {A B : Type'} (f : type1415 A B) : (term67 A B f) = (term68 A B f).
Proof. exact (eq_refl (term67 A B f)). Qed.
Lemma lem6961124 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6961125 {A B : Type'} (f : type1415 A B) : (term69 A B f) = (term70 A B f).
Proof. exact (MK_COMB (@lem6961124) (@lem6961123 A B f)). Qed.
Lemma lem6961126 {A B : Type'} (s : A -> Prop) (f : type1415 A B) : (term71 A B f s) = (term59 A B s f).
Proof. exact (eq_refl (term71 A B f s)). Qed.
Lemma lem6961127 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6961128 {A B : Type'} (s : A -> Prop) (f : type1415 A B) : (term72 A B f s) = (term73 A B s f).
Proof. exact (MK_COMB (@lem6961127) (@lem6961126 A B s f)). Qed.
Lemma lem6961129 {A : Type'} (x : A) (s : A -> Prop) : (term74 A x s) = (term74 A x s).
Proof. exact (eq_refl (term74 A x s)). Qed.
Lemma lem6961130 {A B : Type'} (f : type1415 A B) (x : A) (s : A -> Prop) : (term75 A B f x s) = (term76 A B f x s).
Proof. exact (MK_COMB (@lem6961128 A B s f) (@lem6961129 A x s)). Qed.
Lemma lem6961131 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6961132 {A B : Type'} (f : type1415 A B) (x : A) (s : A -> Prop) : (term77 A B f x s) = (term78 A B f x s).
Proof. exact (MK_COMB (@lem6961131) (@lem6961130 A B f x s)). Qed.
Lemma lem6961133 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) : (term79 A B f x s) = (term80 A B x s f).
Proof. exact (eq_refl (term79 A B f x s)). Qed.
Lemma lem6961134 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) : (term81 A B f x s) = (term82 A B x s f).
Proof. exact (MK_COMB (@lem6961132 A B f x s) (@lem6961133 A B x s f)). Qed.
Lemma lem6961135 {A B : Type'} (x : A) (f : type1415 A B) : (term83 A B f x) = (term84 A B x f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6961134 A B x s f)). Qed.
Lemma lem6961136 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6961137 {A B : Type'} (x : A) (f : type1415 A B) : (term85 A B f x) = (term86 A B x f).
Proof. exact (MK_COMB (@lem6961136 A) (@lem6961135 A B x f)). Qed.
Lemma lem6961138 {A B : Type'} (f : type1415 A B) : (term87 A B f) = (term88 A B f).
Proof. exact (fun_ext (fun x : A => @lem6961137 A B x f)). Qed.
Lemma lem6961139 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6961140 {A B : Type'} (f : type1415 A B) : (term89 A B f) = (term90 A B f).
Proof. exact (MK_COMB (@lem6961139 A) (@lem6961138 A B f)). Qed.
Lemma lem6961141 {A B : Type'} (f : type1415 A B) : (term91 A B f) = (term92 A B f).
Proof. exact (MK_COMB (@lem6961125 A B f) (@lem6961140 A B f)). Qed.
Lemma lem6961142 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6961143 {A B : Type'} (f : type1415 A B) : (term93 A B f) = (term94 A B f).
Proof. exact (MK_COMB (@lem6961142) (@lem6961141 A B f)). Qed.
Lemma lem6961144 {A B : Type'} (s : A -> Prop) (f : type1415 A B) : (term71 A B f s) = (term59 A B s f).
Proof. exact (eq_refl (term71 A B f s)). Qed.
Lemma lem6961145 {A : Type'} (s : A -> Prop) : (term52 A s) = (term52 A s).
Proof. exact (eq_refl (term52 A s)). Qed.
Lemma lem6961146 {A B : Type'} (s : A -> Prop) (f : type1415 A B) : (term95 A B f s) = (term60 A B s f).
Proof. exact (MK_COMB (@lem6961145 A s) (@lem6961144 A B s f)). Qed.
Lemma lem6961147 {A B : Type'} (f : type1415 A B) : (term96 A B f) = (term62 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6961146 A B s f)). Qed.
Lemma lem6961148 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6961149 {A B : Type'} (f : type1415 A B) : (term97 A B f) = (term64 A B f).
Proof. exact (MK_COMB (@lem6961148 A) (@lem6961147 A B f)). Qed.
Lemma lem6961150 {A B : Type'} (f : type1415 A B) : (term65 A B f) = (term98 A B f).
Proof. exact (MK_COMB (@lem6961143 A B f) (@lem6961149 A B f)). Qed.
Lemma lem6961151 {A B : Type'} (f : type1415 A B) : term98 A B f.
Proof. exact (EQ_MP (@lem6961150 A B f) (@lem6961122 A B f)). Qed.
Lemma lem6961161 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term99 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6961162 (p : Prop) (q : Prop) (p' : Prop) : term100 p q p'.
Proof. exact (fun q' : Prop => @lem6961161 p q p' q'). Qed.
Lemma lem6961163 (p : Prop) (q : Prop) : term101 p q.
Proof. exact (fun p' : Prop => @lem6961162 p q p'). Qed.
Lemma lem6961164 {A B : Type'} (t : B -> Prop) (f : type1415 A B) : term102 A B t f.
Proof. exact (@lem6961163 (@FINITE B t) ((term103 A B t f) = (term104 A B t f))). Qed.
Lemma lem6961165 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (p' : Prop) : term105 A B t f p'.
Proof. exact (@lem6961164 A B t f p'). Qed.
Lemma lem6961166 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (p' : Prop) : (term105 A B t f p') = (term106 A B t f p').
Proof. exact (eq_refl (term105 A B t f p')). Qed.
Lemma lem6961167 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (p' : Prop) : term106 A B t f p'.
Proof. exact (EQ_MP (@lem6961166 A B t f p') (@lem6961165 A B t f p')). Qed.
Lemma lem6961168 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (p' : Prop) (q' : Prop) : term107 A B t f p' q'.
Proof. exact (@lem6961167 A B t f p' q'). Qed.
Lemma lem6961169 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (p' : Prop) (q' : Prop) : (term107 A B t f p' q') = (term108 A B t f p' q').
Proof. exact (eq_refl (term107 A B t f p' q')). Qed.
Lemma lem6961170 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (p' : Prop) (q' : Prop) : term108 A B t f p' q'.
Proof. exact (EQ_MP (@lem6961169 A B t f p' q') (@lem6961168 A B t f p' q')). Qed.
Lemma lem6961171 {B : Type'} (t : B -> Prop) : (@FINITE B t) = (@FINITE B t).
Proof. exact (eq_refl (@FINITE B t)). Qed.
Lemma lem6961172 {A B : Type'} (f : type1415 A B) (t : B -> Prop) (q' : Prop) : term109 A B f t q'.
Proof. exact (@lem6961170 A B t f (@FINITE B t) q'). Qed.
Lemma lem6961173 {A B : Type'} (f : type1415 A B) (t : B -> Prop) (q' : Prop) : term110 A B f t q'.
Proof. exact (@lem6961172 A B f t q' (@lem6961171 B t)). Qed.
Lemma lem6961180 {_126486 : Type'} (f : _126486 -> nat) : (@nsum _126486 (@EMPTY _126486) f) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6960976 _126486 f) (@lem6960975 _126486 f)). Qed.
Lemma lem6961181 {A : Type'} (f : A -> nat) : (@nsum A (@EMPTY A) f) = (NUMERAL 0).
Proof. exact (@lem6961180 A f). Qed.
Lemma lem6961182 {A B : Type'} (t : B -> Prop) (f : type1415 A B) : (term103 A B t f) = (NUMERAL 0).
Proof. exact (@lem6961181 A (term111 A B t f)). Qed.
Lemma lem6961183 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6961184 {A B : Type'} (t : B -> Prop) (f : type1415 A B) : (term112 A B t f) = term113.
Proof. exact (MK_COMB (@lem6961183) (@lem6961182 A B t f)). Qed.
Lemma lem6961186 {_126486 : Type'} (f : _126486 -> nat) : (@nsum _126486 (@EMPTY _126486) f) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6960976 _126486 f) (@lem6960975 _126486 f)). Qed.
Lemma lem6961187 {A : Type'} (f : A -> nat) : (@nsum A (@EMPTY A) f) = (NUMERAL 0).
Proof. exact (@lem6961186 A f). Qed.
Lemma lem6961188 {A B : Type'} (f : type1415 A B) (j : B) : (term114 A B f j) = (NUMERAL 0).
Proof. exact (@lem6961187 A (term115 A B f j)). Qed.
Lemma lem6961189 {A B : Type'} (f : type1415 A B) : (term116 A B f) = (term117 B).
Proof. exact (fun_ext (fun j : B => @lem6961188 A B f j)). Qed.
Lemma lem6961190 {B : Type'} (t : B -> Prop) : (@nsum B t) = (@nsum B t).
Proof. exact (eq_refl (@nsum B t)). Qed.
Lemma lem6961191 {A B : Type'} (f : type1415 A B) (t : B -> Prop) : (term104 A B t f) = (term11 B t).
Proof. exact (MK_COMB (@lem6961190 B t) (@lem6961189 A B f)). Qed.
Lemma lem6961193 {A : Type'} (s : A -> Prop) : (term11 A s) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6960955 A s) (@lem6960954 A s)). Qed.
Lemma lem6961194 {B : Type'} (s : B -> Prop) : (term11 B s) = (NUMERAL 0).
Proof. exact (@lem6961193 B s). Qed.
Lemma lem6961195 {B : Type'} (t : B -> Prop) : (term11 B t) = (NUMERAL 0).
Proof. exact (@lem6961194 B t). Qed.
Lemma lem6961196 {A B : Type'} (t : B -> Prop) (f : type1415 A B) : (term104 A B t f) = (NUMERAL 0).
Proof. exact (TRANS (@lem6961191 A B f t) (@lem6961195 B t)). Qed.
Lemma lem6961197 {A B : Type'} (t : B -> Prop) (f : type1415 A B) : ((term103 A B t f) = (term104 A B t f)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem6961184 A B t f) (@lem6961196 A B t f)). Qed.
Lemma lem6961199 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6961200 (x : nat) : (x = x) = True.
Proof. exact (@lem6961199 nat x). Qed.
Lemma lem6961201 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem6961200 (NUMERAL 0)). Qed.
Lemma lem6961202 {A B : Type'} (t : B -> Prop) (f : type1415 A B) : ((term103 A B t f) = (term104 A B t f)) = True.
Proof. exact (TRANS (@lem6961197 A B t f) (@lem6961201)). Qed.
Lemma lem6961203 {A B : Type'} (t : B -> Prop) (f : type1415 A B) : term118 A B t f.
Proof. exact (fun h0 : @FINITE B t => @lem6961202 A B t f). Qed.
Lemma lem6961204 {A B : Type'} (f : type1415 A B) (t : B -> Prop) : term119 A B f t.
Proof. exact (@lem6961173 A B f t True). Qed.
Lemma lem6961205 {A B : Type'} (f : type1415 A B) (t : B -> Prop) : (term120 A B t f) = (term121 B t).
Proof. exact (@lem6961204 A B f t (@lem6961203 A B t f)). Qed.
Lemma lem6961207 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6961208 {B : Type'} (t : B -> Prop) : (term121 B t) = True.
Proof. exact (@lem6961207 (@FINITE B t)). Qed.
Lemma lem6961209 {A B : Type'} (t : B -> Prop) (f : type1415 A B) : (term120 A B t f) = True.
Proof. exact (TRANS (@lem6961205 A B f t) (@lem6961208 B t)). Qed.
Lemma lem6961210 {A B : Type'} (f : type1415 A B) : (term122 A B f) = (term123 B).
Proof. exact (fun_ext (fun t : B -> Prop => @lem6961209 A B t f)). Qed.
Lemma lem6961211 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem6961212 {A B : Type'} (f : type1415 A B) : (term68 A B f) = (term124 B).
Proof. exact (MK_COMB (@lem6961211 B) (@lem6961210 A B f)). Qed.
Lemma lem6961214 {A : Type'} (t : Prop) : (term125 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6961215 {B : Type'} (t : Prop) : (term126 B t) = t.
Proof. exact (@lem6961214 (B -> Prop) t). Qed.
Lemma lem6961216 {B : Type'} : (term124 B) = True.
Proof. exact (@lem6961215 B True). Qed.
Lemma lem6961217 {A B : Type'} (f : type1415 A B) : (term68 A B f) = True.
Proof. exact (TRANS (@lem6961212 A B f) (@lem6961216 B)). Qed.
Lemma lem6961218 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6961219 {A B : Type'} (f : type1415 A B) : (term70 A B f) = (and True).
Proof. exact (MK_COMB (@lem6961218) (@lem6961217 A B f)). Qed.
Lemma lem6961231 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term99 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6961232 (p : Prop) (q : Prop) (p' : Prop) : term100 p q p'.
Proof. exact (fun q' : Prop => @lem6961231 p q p' q'). Qed.
Lemma lem6961233 (p : Prop) (q : Prop) : term101 p q.
Proof. exact (fun p' : Prop => @lem6961232 p q p'). Qed.
Lemma lem6961234 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) : term127 A B x s f.
Proof. exact (@lem6961233 (term76 A B f x s) (term80 A B x s f)). Qed.
Lemma lem6961235 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) (p' : Prop) : term128 A B x s f p'.
Proof. exact (@lem6961234 A B x s f p'). Qed.
Lemma lem6961236 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) (p' : Prop) : (term128 A B x s f p') = (term129 A B x s f p').
Proof. exact (eq_refl (term128 A B x s f p')). Qed.
Lemma lem6961237 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) (p' : Prop) : term129 A B x s f p'.
Proof. exact (EQ_MP (@lem6961236 A B x s f p') (@lem6961235 A B x s f p')). Qed.
Lemma lem6961238 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) (p' : Prop) (q' : Prop) : term130 A B x s f p' q'.
Proof. exact (@lem6961237 A B x s f p' q'). Qed.
Lemma lem6961239 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) (p' : Prop) (q' : Prop) : (term130 A B x s f p' q') = (term131 A B x s f p' q').
Proof. exact (eq_refl (term130 A B x s f p' q')). Qed.
Lemma lem6961240 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) (p' : Prop) (q' : Prop) : term131 A B x s f p' q'.
Proof. exact (EQ_MP (@lem6961239 A B x s f p' q') (@lem6961238 A B x s f p' q')). Qed.
Lemma lem6961276 {A B : Type'} (f : type1415 A B) (x : A) (s : A -> Prop) : (term76 A B f x s) = (term76 A B f x s).
Proof. exact (eq_refl (term76 A B f x s)). Qed.
Lemma lem6961277 {A B : Type'} (f : type1415 A B) (x : A) (s : A -> Prop) (q' : Prop) : term132 A B f x s q'.
Proof. exact (@lem6961240 A B x s f (term76 A B f x s) q'). Qed.
Lemma lem6961278 {A B : Type'} (f : type1415 A B) (x : A) (s : A -> Prop) (q' : Prop) : term133 A B f x s q'.
Proof. exact (@lem6961277 A B f x s q' (@lem6961276 A B f x s)). Qed.
Lemma lem6961279 {A B : Type'} (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : term76 A B f x s.
Proof. exact (h1). Qed.
Lemma lem6961280 {A B : Type'} (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : term74 A x s.
Proof. exact (proj2 (@lem6961279 A B f x s h1)). Qed.
Lemma lem6961281 {A B : Type'} (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : @FINITE A s.
Proof. exact (proj2 (@lem6961280 A B f x s h1)). Qed.
Lemma lem6961282 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem6961284 {A B : Type'} (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : term134 A x s.
Proof. exact (proj1 (@lem6961280 A B f x s h1)). Qed.
Lemma lem6961285 {A : Type'} (x : A) (s : A -> Prop) : term135 A x s.
Proof. exact (@lem82 (@IN A x s)). Qed.
Lemma lem6961287 {A B : Type'} (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : term59 A B s f.
Proof. exact (proj1 (@lem6961279 A B f x s h1)). Qed.
Lemma lem6961288 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : term50 A B s f t.
Proof. exact (@lem6961287 A B f x s h1 t). Qed.
Lemma lem6961289 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : type1415 A B) : (term50 A B s f t) = (term51 A B t s f).
Proof. exact (eq_refl (term50 A B s f t)). Qed.
Lemma lem6961290 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : term51 A B t s f.
Proof. exact (EQ_MP (@lem6961289 A B t s f) (@lem6961288 A B t f x s h1)). Qed.
Lemma lem6961291 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (h1). Qed.
Lemma lem6961292 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term76 A B f x s) : (term39 A B s t f) = (term40 A B t s f).
Proof. exact (@lem6961290 A B t f x s h2 (@lem6961291 B t h1)). Qed.
Lemma lem6961305 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term99 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6961306 (p : Prop) (q : Prop) (p' : Prop) : term100 p q p'.
Proof. exact (fun q' : Prop => @lem6961305 p q p' q'). Qed.
Lemma lem6961307 (p : Prop) (q : Prop) : term101 p q.
Proof. exact (fun p' : Prop => @lem6961306 p q p'). Qed.
Lemma lem6961308 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : type1415 A B) : term136 A B t x s f.
Proof. exact (@lem6961307 (@FINITE B t) ((term137 A B x s t f) = (term138 A B t x s f))). Qed.
Lemma lem6961309 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : type1415 A B) (p' : Prop) : term139 A B t x s f p'.
Proof. exact (@lem6961308 A B t x s f p'). Qed.
Lemma lem6961310 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : type1415 A B) (p' : Prop) : (term139 A B t x s f p') = (term140 A B t x s f p').
Proof. exact (eq_refl (term139 A B t x s f p')). Qed.
Lemma lem6961311 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : type1415 A B) (p' : Prop) : term140 A B t x s f p'.
Proof. exact (EQ_MP (@lem6961310 A B t x s f p') (@lem6961309 A B t x s f p')). Qed.
Lemma lem6961312 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : type1415 A B) (p' : Prop) (q' : Prop) : term141 A B t x s f p' q'.
Proof. exact (@lem6961311 A B t x s f p' q'). Qed.
Lemma lem6961313 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : type1415 A B) (p' : Prop) (q' : Prop) : (term141 A B t x s f p' q') = (term142 A B t x s f p' q').
Proof. exact (eq_refl (term141 A B t x s f p' q')). Qed.
Lemma lem6961314 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : type1415 A B) (p' : Prop) (q' : Prop) : term142 A B t x s f p' q'.
Proof. exact (EQ_MP (@lem6961313 A B t x s f p' q') (@lem6961312 A B t x s f p' q')). Qed.
Lemma lem6961315 {B : Type'} (t : B -> Prop) : (@FINITE B t) = (@FINITE B t).
Proof. exact (eq_refl (@FINITE B t)). Qed.
Lemma lem6961316 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) (t : B -> Prop) (q' : Prop) : term143 A B x s f t q'.
Proof. exact (@lem6961314 A B t x s f (@FINITE B t) q'). Qed.
Lemma lem6961317 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) (t : B -> Prop) (q' : Prop) : term144 A B x s f t q'.
Proof. exact (@lem6961316 A B x s f t q' (@lem6961315 B t)). Qed.
Lemma lem6961318 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (h1). Qed.
Lemma lem6961319 {B : Type'} (t : B -> Prop) : (@FINITE B t) = ((@FINITE B t) = True).
Proof. exact (@lem7 (@FINITE B t)). Qed.
Lemma lem6961324 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : term18 _126525 x s f.
Proof. exact (fun h0 : @FINITE _126525 s => @lem6960968 _126525 x f s h0). Qed.
Lemma lem6961325 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) : term18 A x s f.
Proof. exact (@lem6961324 A x s f). Qed.
Lemma lem6961326 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : type1415 A B) : term145 A B x s t f.
Proof. exact (@lem6961325 A x s (term111 A B t f)). Qed.
Lemma lem6961328 {A B : Type'} (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem6961282 A s) (@lem6961281 A B f x s h1)). Qed.
Lemma lem6961329 {A B : Type'} (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : True = (@FINITE A s).
Proof. exact (SYM (@lem6961328 A B f x s h1)). Qed.
Lemma lem6961330 {A B : Type'} (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : @FINITE A s.
Proof. exact (EQ_MP (@lem6961329 A B f x s h1) (@lem0)). Qed.
Lemma lem6961331 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : (term137 A B x s t f) = (term146 A B x s t f).
Proof. exact (@lem6961326 A B x s t f (@lem6961330 A B f x s h1)). Qed.
Lemma lem6961333 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term147 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem6961334 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term148 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem6961333 _2963 g t e g' t' e'). Qed.
Lemma lem6961335 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term149 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem6961334 _2963 g t e g' t'). Qed.
Lemma lem6961336 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term150 _2963 g t e.
Proof. exact (fun g' : Prop => @lem6961335 _2963 g t e g'). Qed.
Lemma lem6961337 (g : Prop) (t : nat) (e : nat) : term151 g t e.
Proof. exact (@lem6961336 nat g t e). Qed.
Lemma lem6961338 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : type1415 A B) : term152 A B x s t f.
Proof. exact (@lem6961337 (@IN A x s) (term39 A B s t f) (term153 A B x s t f)). Qed.
Lemma lem6961339 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : type1415 A B) (g' : Prop) : term154 A B x s t f g'.
Proof. exact (@lem6961338 A B x s t f g'). Qed.
Lemma lem6961340 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : type1415 A B) (g' : Prop) : (term154 A B x s t f g') = (term155 A B x s t f g').
Proof. exact (eq_refl (term154 A B x s t f g')). Qed.
Lemma lem6961341 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : type1415 A B) (g' : Prop) : term155 A B x s t f g'.
Proof. exact (EQ_MP (@lem6961340 A B x s t f g') (@lem6961339 A B x s t f g')). Qed.
Lemma lem6961342 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : type1415 A B) (g' : Prop) (t' : nat) : term156 A B x s t f g' t'.
Proof. exact (@lem6961341 A B x s t f g' t'). Qed.
Lemma lem6961343 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : type1415 A B) (g' : Prop) (t' : nat) : (term156 A B x s t f g' t') = (term157 A B x s t f g' t').
Proof. exact (eq_refl (term156 A B x s t f g' t')). Qed.
Lemma lem6961344 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : type1415 A B) (g' : Prop) (t' : nat) : term157 A B x s t f g' t'.
Proof. exact (EQ_MP (@lem6961343 A B x s t f g' t') (@lem6961342 A B x s t f g' t')). Qed.
Lemma lem6961345 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : type1415 A B) (g' : Prop) (t' : nat) (e' : nat) : term158 A B x s t f g' t' e'.
Proof. exact (@lem6961344 A B x s t f g' t' e'). Qed.
Lemma lem6961346 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : type1415 A B) (g' : Prop) (t' : nat) (e' : nat) : (term158 A B x s t f g' t' e') = (term159 A B x s t f g' t' e').
Proof. exact (eq_refl (term158 A B x s t f g' t' e')). Qed.
Lemma lem6961347 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : type1415 A B) (g' : Prop) (t' : nat) (e' : nat) : term159 A B x s t f g' t' e'.
Proof. exact (EQ_MP (@lem6961346 A B x s t f g' t' e') (@lem6961345 A B x s t f g' t' e')). Qed.
Lemma lem6961349 {A B : Type'} (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : (@IN A x s) = False.
Proof. exact (@lem6961285 A x s (@lem6961284 A B f x s h1)). Qed.
Lemma lem6961350 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : type1415 A B) (t' : nat) (e' : nat) : term160 A B x s t f t' e'.
Proof. exact (@lem6961347 A B x s t f False t' e'). Qed.
Lemma lem6961351 {A B : Type'} (t : B -> Prop) (t' : nat) (e' : nat) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : term161 A B x s t f t' e'.
Proof. exact (@lem6961350 A B x s t f t' e' (@lem6961349 A B f x s h1)). Qed.
Lemma lem6961356 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : term51 A B t s f.
Proof. exact (fun h0 : @FINITE B t => @lem6961292 A B t f x s h0 h1). Qed.
Lemma lem6961357 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : term51 A B t s f.
Proof. exact (@lem6961356 A B t f x s h1). Qed.
Lemma lem6961359 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : (@FINITE B t) = True.
Proof. exact (EQ_MP (@lem6961319 B t) (@lem6961318 B t h1)). Qed.
Lemma lem6961360 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : True = (@FINITE B t).
Proof. exact (SYM (@lem6961359 B t h1)). Qed.
Lemma lem6961361 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (EQ_MP (@lem6961360 B t h1) (@lem0)). Qed.
Lemma lem6961362 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term76 A B f x s) : (term39 A B s t f) = (term40 A B t s f).
Proof. exact (@lem6961357 A B t f x s h2 (@lem6961361 B t h1)). Qed.
Lemma lem6961363 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term76 A B f x s) : term162 A B t s f.
Proof. exact (fun h0 : False => @lem6961362 A B t f x s h1 h2). Qed.
Lemma lem6961364 {A B : Type'} (t : B -> Prop) (e' : nat) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : term163 A B x t s f e'.
Proof. exact (@lem6961351 A B t (term40 A B t s f) e' f x s h1). Qed.
Lemma lem6961365 {A B : Type'} (e' : nat) (t : B -> Prop) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term76 A B f x s) : term164 A B x t s f e'.
Proof. exact (@lem6961364 A B t e' f x s h2 (@lem6961363 A B t f x s h1 h2)). Qed.
Lemma lem6961372 {A B : Type'} (f : A -> B) (y : A) : (term165 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6961373 {A : Type'} (f : A -> nat) (y : A) : (term166 A f y) = (f y).
Proof. exact (@lem6961372 A nat f y). Qed.
Lemma lem6961374 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) : (term167 A B t f x) = (term168 A B t f x).
Proof. exact (@lem6961373 A (term111 A B t f) x). Qed.
Lemma lem6961375 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (i : A) : (term168 A B t f i) = (term169 A B t f i).
Proof. exact (eq_refl (term168 A B t f i)). Qed.
Lemma lem6961376 {A B : Type'} (t : B -> Prop) (f : type1415 A B) : (term170 A B t f) = (term111 A B t f).
Proof. exact (fun_ext (fun i : A => @lem6961375 A B t f i)). Qed.
Lemma lem6961377 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6961378 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) : (term167 A B t f x) = (term168 A B t f x).
Proof. exact (MK_COMB (@lem6961376 A B t f) (@lem6961377 A x)). Qed.
Lemma lem6961379 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6961380 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) : (term171 A B t f x) = (term172 A B t f x).
Proof. exact (MK_COMB (@lem6961379) (@lem6961378 A B t f x)). Qed.
Lemma lem6961381 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) : (term168 A B t f x) = (term169 A B t f x).
Proof. exact (eq_refl (term168 A B t f x)). Qed.
Lemma lem6961382 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) : ((term167 A B t f x) = (term168 A B t f x)) = ((term168 A B t f x) = (term169 A B t f x)).
Proof. exact (MK_COMB (@lem6961380 A B t f x) (@lem6961381 A B t f x)). Qed.
Lemma lem6961383 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) : (term168 A B t f x) = (term169 A B t f x).
Proof. exact (EQ_MP (@lem6961382 A B t f x) (@lem6961374 A B t f x)). Qed.
Lemma lem6961384 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem6961385 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) : (term173 A B t f x) = (term174 A B t f x).
Proof. exact (MK_COMB (@lem6961384) (@lem6961383 A B t f x)). Qed.
Lemma lem6961387 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : term51 A B t s f.
Proof. exact (fun h0 : @FINITE B t => @lem6961292 A B t f x s h0 h1). Qed.
Lemma lem6961388 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : term51 A B t s f.
Proof. exact (@lem6961387 A B t f x s h1). Qed.
Lemma lem6961390 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : (@FINITE B t) = True.
Proof. exact (EQ_MP (@lem6961319 B t) (@lem6961318 B t h1)). Qed.
Lemma lem6961391 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : True = (@FINITE B t).
Proof. exact (SYM (@lem6961390 B t h1)). Qed.
Lemma lem6961392 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (EQ_MP (@lem6961391 B t h1) (@lem0)). Qed.
Lemma lem6961393 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term76 A B f x s) : (term39 A B s t f) = (term40 A B t s f).
Proof. exact (@lem6961388 A B t f x s h2 (@lem6961392 B t h1)). Qed.
Lemma lem6961394 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term76 A B f x s) : (term153 A B x s t f) = (term175 A B x t s f).
Proof. exact (MK_COMB (@lem6961385 A B t f x) (@lem6961393 A B t f x s h1 h2)). Qed.
Lemma lem6961395 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term76 A B f x s) : term176 A B x t s f.
Proof. exact (fun h0 : ~ False => @lem6961394 A B t f x s h1 h2). Qed.
Lemma lem6961396 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term76 A B f x s) : term177 A B x t s f.
Proof. exact (@lem6961365 A B (term175 A B x t s f) t f x s h1 h2). Qed.
Lemma lem6961397 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term76 A B f x s) : (term146 A B x s t f) = (term178 A B x t s f).
Proof. exact (@lem6961396 A B t f x s h1 h2 (@lem6961395 A B t f x s h1 h2)). Qed.
Lemma lem6961399 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6961400 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem6961399 nat t1 t2). Qed.
Lemma lem6961401 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : type1415 A B) : (term178 A B x t s f) = (term175 A B x t s f).
Proof. exact (@lem6961400 (term40 A B t s f) (term175 A B x t s f)). Qed.
Lemma lem6961402 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term76 A B f x s) : (term146 A B x s t f) = (term175 A B x t s f).
Proof. exact (TRANS (@lem6961397 A B t f x s h1 h2) (@lem6961401 A B x t s f)). Qed.
Lemma lem6961403 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term76 A B f x s) : (term137 A B x s t f) = (term175 A B x t s f).
Proof. exact (TRANS (@lem6961331 A B t f x s h2) (@lem6961402 A B t f x s h1 h2)). Qed.
Lemma lem6961404 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6961405 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term76 A B f x s) : (term179 A B x s t f) = (term180 A B x t s f).
Proof. exact (MK_COMB (@lem6961404) (@lem6961403 A B t f x s h1 h2)). Qed.
Lemma lem6961407 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : term18 _126525 x s f.
Proof. exact (fun h0 : @FINITE _126525 s => @lem6960968 _126525 x f s h0). Qed.
Lemma lem6961408 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) : term18 A x s f.
Proof. exact (@lem6961407 A x s f). Qed.
Lemma lem6961409 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) (j : B) : term181 A B x s f j.
Proof. exact (@lem6961408 A x s (term115 A B f j)). Qed.
Lemma lem6961411 {A B : Type'} (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem6961282 A s) (@lem6961281 A B f x s h1)). Qed.
Lemma lem6961412 {A B : Type'} (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : True = (@FINITE A s).
Proof. exact (SYM (@lem6961411 A B f x s h1)). Qed.
Lemma lem6961413 {A B : Type'} (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : @FINITE A s.
Proof. exact (EQ_MP (@lem6961412 A B f x s h1) (@lem0)). Qed.
Lemma lem6961414 {A B : Type'} (j : B) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : (term182 A B x s f j) = (term183 A B x s f j).
Proof. exact (@lem6961409 A B x s f j (@lem6961413 A B f x s h1)). Qed.
Lemma lem6961416 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term147 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem6961417 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term148 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem6961416 _2963 g t e g' t' e'). Qed.
Lemma lem6961418 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term149 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem6961417 _2963 g t e g' t'). Qed.
Lemma lem6961419 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term150 _2963 g t e.
Proof. exact (fun g' : Prop => @lem6961418 _2963 g t e g'). Qed.
Lemma lem6961420 (g : Prop) (t : nat) (e : nat) : term151 g t e.
Proof. exact (@lem6961419 nat g t e). Qed.
Lemma lem6961421 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) (j : B) : term184 A B x s f j.
Proof. exact (@lem6961420 (@IN A x s) (term185 A B s f j) (term186 A B x s f j)). Qed.
Lemma lem6961422 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) (j : B) (g' : Prop) : term187 A B x s f j g'.
Proof. exact (@lem6961421 A B x s f j g'). Qed.
Lemma lem6961423 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) (j : B) (g' : Prop) : (term187 A B x s f j g') = (term188 A B x s f j g').
Proof. exact (eq_refl (term187 A B x s f j g')). Qed.
Lemma lem6961424 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) (j : B) (g' : Prop) : term188 A B x s f j g'.
Proof. exact (EQ_MP (@lem6961423 A B x s f j g') (@lem6961422 A B x s f j g')). Qed.
Lemma lem6961425 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) (j : B) (g' : Prop) (t' : nat) : term189 A B x s f j g' t'.
Proof. exact (@lem6961424 A B x s f j g' t'). Qed.
Lemma lem6961426 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) (j : B) (g' : Prop) (t' : nat) : (term189 A B x s f j g' t') = (term190 A B x s f j g' t').
Proof. exact (eq_refl (term189 A B x s f j g' t')). Qed.
Lemma lem6961427 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) (j : B) (g' : Prop) (t' : nat) : term190 A B x s f j g' t'.
Proof. exact (EQ_MP (@lem6961426 A B x s f j g' t') (@lem6961425 A B x s f j g' t')). Qed.
Lemma lem6961428 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) (j : B) (g' : Prop) (t' : nat) (e' : nat) : term191 A B x s f j g' t' e'.
Proof. exact (@lem6961427 A B x s f j g' t' e'). Qed.
Lemma lem6961429 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) (j : B) (g' : Prop) (t' : nat) (e' : nat) : (term191 A B x s f j g' t' e') = (term192 A B x s f j g' t' e').
Proof. exact (eq_refl (term191 A B x s f j g' t' e')). Qed.
Lemma lem6961430 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) (j : B) (g' : Prop) (t' : nat) (e' : nat) : term192 A B x s f j g' t' e'.
Proof. exact (EQ_MP (@lem6961429 A B x s f j g' t' e') (@lem6961428 A B x s f j g' t' e')). Qed.
Lemma lem6961432 {A B : Type'} (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : (@IN A x s) = False.
Proof. exact (@lem6961285 A x s (@lem6961284 A B f x s h1)). Qed.
Lemma lem6961433 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) (j : B) (t' : nat) (e' : nat) : term193 A B x s f j t' e'.
Proof. exact (@lem6961430 A B x s f j False t' e'). Qed.
Lemma lem6961434 {A B : Type'} (j : B) (t' : nat) (e' : nat) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : term194 A B x s f j t' e'.
Proof. exact (@lem6961433 A B x s f j t' e' (@lem6961432 A B f x s h1)). Qed.
Lemma lem6961438 {A B : Type'} (s : A -> Prop) (f : type1415 A B) (j : B) : (term185 A B s f j) = (term185 A B s f j).
Proof. exact (eq_refl (term185 A B s f j)). Qed.
Lemma lem6961439 {A B : Type'} (s : A -> Prop) (f : type1415 A B) (j : B) : term195 A B s f j.
Proof. exact (fun h0 : False => @lem6961438 A B s f j). Qed.
Lemma lem6961440 {A B : Type'} (j : B) (e' : nat) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : term196 A B x s f j e'.
Proof. exact (@lem6961434 A B j (term185 A B s f j) e' f x s h1). Qed.
Lemma lem6961441 {A B : Type'} (j : B) (e' : nat) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : term197 A B x s f j e'.
Proof. exact (@lem6961440 A B j e' f x s h1 (@lem6961439 A B s f j)). Qed.
Lemma lem6961448 {A B : Type'} (f : A -> B) (y : A) : (term165 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6961449 {A : Type'} (f : A -> nat) (y : A) : (term166 A f y) = (f y).
Proof. exact (@lem6961448 A nat f y). Qed.
Lemma lem6961450 {A B : Type'} (f : type1415 A B) (j : B) (x : A) : (term198 A B f j x) = (term199 A B f j x).
Proof. exact (@lem6961449 A (term115 A B f j) x). Qed.
Lemma lem6961451 {A B : Type'} (f : type1415 A B) (i : A) (j : B) : (term199 A B f j i) = (f i j).
Proof. exact (eq_refl (term199 A B f j i)). Qed.
Lemma lem6961452 {A B : Type'} (f : type1415 A B) (j : B) : (term200 A B f j) = (term115 A B f j).
Proof. exact (fun_ext (fun i : A => @lem6961451 A B f i j)). Qed.
Lemma lem6961453 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6961454 {A B : Type'} (f : type1415 A B) (j : B) (x : A) : (term198 A B f j x) = (term199 A B f j x).
Proof. exact (MK_COMB (@lem6961452 A B f j) (@lem6961453 A x)). Qed.
Lemma lem6961455 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6961456 {A B : Type'} (f : type1415 A B) (j : B) (x : A) : (term201 A B f j x) = (term202 A B f j x).
Proof. exact (MK_COMB (@lem6961455) (@lem6961454 A B f j x)). Qed.
Lemma lem6961457 {A B : Type'} (f : type1415 A B) (x : A) (j : B) : (term199 A B f j x) = (f x j).
Proof. exact (eq_refl (term199 A B f j x)). Qed.
Lemma lem6961458 {A B : Type'} (f : type1415 A B) (x : A) (j : B) : ((term198 A B f j x) = (term199 A B f j x)) = ((term199 A B f j x) = (f x j)).
Proof. exact (MK_COMB (@lem6961456 A B f j x) (@lem6961457 A B f x j)). Qed.
Lemma lem6961459 {A B : Type'} (f : type1415 A B) (x : A) (j : B) : (term199 A B f j x) = (f x j).
Proof. exact (EQ_MP (@lem6961458 A B f x j) (@lem6961450 A B f j x)). Qed.
Lemma lem6961460 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem6961461 {A B : Type'} (f : type1415 A B) (x : A) (j : B) : (term203 A B f j x) = (term204 A B f x j).
Proof. exact (MK_COMB (@lem6961460) (@lem6961459 A B f x j)). Qed.
Lemma lem6961462 {A B : Type'} (s : A -> Prop) (f : type1415 A B) (j : B) : (term185 A B s f j) = (term185 A B s f j).
Proof. exact (eq_refl (term185 A B s f j)). Qed.
Lemma lem6961463 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) (j : B) : (term186 A B x s f j) = (term205 A B x s f j).
Proof. exact (MK_COMB (@lem6961461 A B f x j) (@lem6961462 A B s f j)). Qed.
Lemma lem6961464 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) (j : B) : term206 A B x s f j.
Proof. exact (fun h0 : ~ False => @lem6961463 A B x s f j). Qed.
Lemma lem6961465 {A B : Type'} (j : B) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : term207 A B x s f j.
Proof. exact (@lem6961441 A B j (term205 A B x s f j) f x s h1). Qed.
Lemma lem6961466 {A B : Type'} (j : B) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : (term183 A B x s f j) = (term208 A B x s f j).
Proof. exact (@lem6961465 A B j f x s h1 (@lem6961464 A B x s f j)). Qed.
Lemma lem6961468 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6961469 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem6961468 nat t1 t2). Qed.
Lemma lem6961470 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) (j : B) : (term208 A B x s f j) = (term205 A B x s f j).
Proof. exact (@lem6961469 (term185 A B s f j) (term205 A B x s f j)). Qed.
Lemma lem6961471 {A B : Type'} (j : B) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : (term183 A B x s f j) = (term205 A B x s f j).
Proof. exact (TRANS (@lem6961466 A B j f x s h1) (@lem6961470 A B x s f j)). Qed.
Lemma lem6961472 {A B : Type'} (j : B) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : (term182 A B x s f j) = (term205 A B x s f j).
Proof. exact (TRANS (@lem6961414 A B j f x s h1) (@lem6961471 A B j f x s h1)). Qed.
Lemma lem6961473 {A B : Type'} (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : (term209 A B x s f) = (term210 A B x s f).
Proof. exact (fun_ext (fun j : B => @lem6961472 A B j f x s h1)). Qed.
Lemma lem6961474 {B : Type'} (t : B -> Prop) : (@nsum B t) = (@nsum B t).
Proof. exact (eq_refl (@nsum B t)). Qed.
Lemma lem6961475 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : (term138 A B t x s f) = (term211 A B t x s f).
Proof. exact (MK_COMB (@lem6961474 B t) (@lem6961473 A B f x s h1)). Qed.
Lemma lem6961477 {_126729 : Type'} (f : _126729 -> nat) (s : _126729 -> Prop) (g : _126729 -> nat) : term7 _126729 f s g.
Proof. exact (fun h0 : @FINITE _126729 s => @lem6960948 _126729 f g s h0). Qed.
Lemma lem6961478 {B : Type'} (f : B -> nat) (s : B -> Prop) (g : B -> nat) : term7 B f s g.
Proof. exact (@lem6961477 B f s g). Qed.
Lemma lem6961479 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : type1415 A B) : term212 A B x t s f.
Proof. exact (@lem6961478 B (term213 A B f x) t (term214 A B s f)). Qed.
Lemma lem6961480 {A B : Type'} (f : type1415 A B) (x : A) (j : B) : (term215 A B f x j) = (f x j).
Proof. exact (eq_refl (term215 A B f x j)). Qed.
Lemma lem6961481 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem6961482 {A B : Type'} (f : type1415 A B) (x : A) (j : B) : (term216 A B f x j) = (term204 A B f x j).
Proof. exact (MK_COMB (@lem6961481) (@lem6961480 A B f x j)). Qed.
Lemma lem6961483 {A B : Type'} (s : A -> Prop) (f : type1415 A B) (j : B) : (term217 A B s f j) = (term185 A B s f j).
Proof. exact (eq_refl (term217 A B s f j)). Qed.
Lemma lem6961484 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) (j : B) : (term218 A B x s f j) = (term205 A B x s f j).
Proof. exact (MK_COMB (@lem6961482 A B f x j) (@lem6961483 A B s f j)). Qed.
Lemma lem6961485 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) : (term219 A B x s f) = (term210 A B x s f).
Proof. exact (fun_ext (fun j : B => @lem6961484 A B x s f j)). Qed.
Lemma lem6961486 {B : Type'} (t : B -> Prop) : (@nsum B t) = (@nsum B t).
Proof. exact (eq_refl (@nsum B t)). Qed.
Lemma lem6961487 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : type1415 A B) : (term220 A B t x s f) = (term211 A B t x s f).
Proof. exact (MK_COMB (@lem6961486 B t) (@lem6961485 A B x s f)). Qed.
Lemma lem6961488 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6961489 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : type1415 A B) : (term221 A B t x s f) = (term222 A B t x s f).
Proof. exact (MK_COMB (@lem6961488) (@lem6961487 A B t x s f)). Qed.
Lemma lem6961490 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : type1415 A B) : (term223 A B x t s f) = (term223 A B x t s f).
Proof. exact (eq_refl (term223 A B x t s f)). Qed.
Lemma lem6961491 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : type1415 A B) : ((term220 A B t x s f) = (term223 A B x t s f)) = ((term211 A B t x s f) = (term223 A B x t s f)).
Proof. exact (MK_COMB (@lem6961489 A B t x s f) (@lem6961490 A B x t s f)). Qed.
Lemma lem6961492 {B : Type'} (t : B -> Prop) : (term52 B t) = (term52 B t).
Proof. exact (eq_refl (term52 B t)). Qed.
Lemma lem6961493 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : type1415 A B) : (term212 A B x t s f) = (term224 A B x t s f).
Proof. exact (MK_COMB (@lem6961492 B t) (@lem6961491 A B x t s f)). Qed.
Lemma lem6961494 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : type1415 A B) : term224 A B x t s f.
Proof. exact (EQ_MP (@lem6961493 A B x t s f) (@lem6961479 A B x t s f)). Qed.
Lemma lem6961496 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : (@FINITE B t) = True.
Proof. exact (EQ_MP (@lem6961319 B t) (@lem6961318 B t h1)). Qed.
Lemma lem6961497 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : True = (@FINITE B t).
Proof. exact (SYM (@lem6961496 B t h1)). Qed.
Lemma lem6961498 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (EQ_MP (@lem6961497 B t h1) (@lem0)). Qed.
Lemma lem6961499 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) (t : B -> Prop) (h1 : @FINITE B t) : (term211 A B t x s f) = (term223 A B x t s f).
Proof. exact (@lem6961494 A B x t s f (@lem6961498 B t h1)). Qed.
Lemma lem6961500 {B : Type'} (t : B -> nat) : (term225 B t) = t.
Proof. exact (@lem6960937 B nat t). Qed.
Lemma lem6961501 {A B : Type'} (f : type1415 A B) (x : A) : (term213 A B f x) = (f x).
Proof. exact (@lem6961500 B (f x)). Qed.
Lemma lem6961502 {B : Type'} (t : B -> Prop) : (@nsum B t) = (@nsum B t).
Proof. exact (eq_refl (@nsum B t)). Qed.
Lemma lem6961503 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) : (term226 A B t f x) = (term169 A B t f x).
Proof. exact (MK_COMB (@lem6961502 B t) (@lem6961501 A B f x)). Qed.
Lemma lem6961504 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem6961505 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) : (term227 A B t f x) = (term174 A B t f x).
Proof. exact (MK_COMB (@lem6961504) (@lem6961503 A B t f x)). Qed.
Lemma lem6961506 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : type1415 A B) : (term40 A B t s f) = (term40 A B t s f).
Proof. exact (eq_refl (term40 A B t s f)). Qed.
Lemma lem6961507 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : type1415 A B) : (term223 A B x t s f) = (term175 A B x t s f).
Proof. exact (MK_COMB (@lem6961505 A B t f x) (@lem6961506 A B t s f)). Qed.
Lemma lem6961508 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) (t : B -> Prop) (h1 : @FINITE B t) : (term211 A B t x s f) = (term175 A B x t s f).
Proof. exact (TRANS (@lem6961499 A B x s f t h1) (@lem6961507 A B x t s f)). Qed.
Lemma lem6961509 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term76 A B f x s) : (term138 A B t x s f) = (term175 A B x t s f).
Proof. exact (TRANS (@lem6961475 A B t f x s h2) (@lem6961508 A B x s f t h1)). Qed.
Lemma lem6961510 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term76 A B f x s) : ((term137 A B x s t f) = (term138 A B t x s f)) = ((term175 A B x t s f) = (term175 A B x t s f)).
Proof. exact (MK_COMB (@lem6961405 A B t f x s h1 h2) (@lem6961509 A B t f x s h1 h2)). Qed.
Lemma lem6961512 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6961513 (x : nat) : (x = x) = True.
Proof. exact (@lem6961512 nat x). Qed.
Lemma lem6961514 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : type1415 A B) : ((term175 A B x t s f) = (term175 A B x t s f)) = True.
Proof. exact (@lem6961513 (term175 A B x t s f)). Qed.
Lemma lem6961515 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term76 A B f x s) : ((term137 A B x s t f) = (term138 A B t x s f)) = True.
Proof. exact (TRANS (@lem6961510 A B t f x s h1 h2) (@lem6961514 A B x t s f)). Qed.
Lemma lem6961516 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : term228 A B t x s f.
Proof. exact (fun h0 : @FINITE B t => @lem6961515 A B t f x s h0 h1). Qed.
Lemma lem6961517 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) (t : B -> Prop) : term229 A B x s f t.
Proof. exact (@lem6961317 A B x s f t True). Qed.
Lemma lem6961518 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : (term230 A B t x s f) = (term121 B t).
Proof. exact (@lem6961517 A B x s f t (@lem6961516 A B t f x s h1)). Qed.
Lemma lem6961520 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6961521 {B : Type'} (t : B -> Prop) : (term121 B t) = True.
Proof. exact (@lem6961520 (@FINITE B t)). Qed.
Lemma lem6961522 {A B : Type'} (t : B -> Prop) (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : (term230 A B t x s f) = True.
Proof. exact (TRANS (@lem6961518 A B t f x s h1) (@lem6961521 B t)). Qed.
Lemma lem6961523 {A B : Type'} (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : (term231 A B x s f) = (term123 B).
Proof. exact (fun_ext (fun t : B -> Prop => @lem6961522 A B t f x s h1)). Qed.
Lemma lem6961524 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem6961525 {A B : Type'} (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : (term80 A B x s f) = (term124 B).
Proof. exact (MK_COMB (@lem6961524 B) (@lem6961523 A B f x s h1)). Qed.
Lemma lem6961527 {A : Type'} (t : Prop) : (term125 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6961528 {B : Type'} (t : Prop) : (term126 B t) = t.
Proof. exact (@lem6961527 (B -> Prop) t). Qed.
Lemma lem6961529 {B : Type'} : (term124 B) = True.
Proof. exact (@lem6961528 B True). Qed.
Lemma lem6961530 {A B : Type'} (f : type1415 A B) (x : A) (s : A -> Prop) (h1 : term76 A B f x s) : (term80 A B x s f) = True.
Proof. exact (TRANS (@lem6961525 A B f x s h1) (@lem6961529 B)). Qed.
Lemma lem6961531 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) : term232 A B x s f.
Proof. exact (fun h0 : term76 A B f x s => @lem6961530 A B f x s h0). Qed.
Lemma lem6961532 {A B : Type'} (f : type1415 A B) (x : A) (s : A -> Prop) : term233 A B f x s.
Proof. exact (@lem6961278 A B f x s True). Qed.
Lemma lem6961533 {A B : Type'} (f : type1415 A B) (x : A) (s : A -> Prop) : (term82 A B x s f) = (term234 A B f x s).
Proof. exact (@lem6961532 A B f x s (@lem6961531 A B x s f)). Qed.
Lemma lem6961535 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6961536 {A B : Type'} (f : type1415 A B) (x : A) (s : A -> Prop) : (term234 A B f x s) = True.
Proof. exact (@lem6961535 (term76 A B f x s)). Qed.
Lemma lem6961537 {A B : Type'} (x : A) (s : A -> Prop) (f : type1415 A B) : (term82 A B x s f) = True.
Proof. exact (TRANS (@lem6961533 A B f x s) (@lem6961536 A B f x s)). Qed.
Lemma lem6961538 {A B : Type'} (x : A) (f : type1415 A B) : (term84 A B x f) = (term123 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6961537 A B x s f)). Qed.
Lemma lem6961539 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6961540 {A B : Type'} (x : A) (f : type1415 A B) : (term86 A B x f) = (term124 A).
Proof. exact (MK_COMB (@lem6961539 A) (@lem6961538 A B x f)). Qed.
Lemma lem6961542 {A : Type'} (t : Prop) : (term125 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6961543 {A : Type'} (t : Prop) : (term126 A t) = t.
Proof. exact (@lem6961542 (A -> Prop) t). Qed.
Lemma lem6961544 {A : Type'} : (term124 A) = True.
Proof. exact (@lem6961543 A True). Qed.
Lemma lem6961545 {A B : Type'} (x : A) (f : type1415 A B) : (term86 A B x f) = True.
Proof. exact (TRANS (@lem6961540 A B x f) (@lem6961544 A)). Qed.
Lemma lem6961546 {A B : Type'} (f : type1415 A B) : (term88 A B f) = (term235 A).
Proof. exact (fun_ext (fun x : A => @lem6961545 A B x f)). Qed.
Lemma lem6961547 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6961548 {A B : Type'} (f : type1415 A B) : (term90 A B f) = (term236 A).
Proof. exact (MK_COMB (@lem6961547 A) (@lem6961546 A B f)). Qed.
Lemma lem6961550 {A : Type'} (t : Prop) : (term125 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6961551 {A : Type'} (t : Prop) : (term125 A t) = t.
Proof. exact (@lem6961550 A t). Qed.
Lemma lem6961552 {A : Type'} : (term236 A) = True.
Proof. exact (@lem6961551 A True). Qed.
Lemma lem6961553 {A B : Type'} (f : type1415 A B) : (term90 A B f) = True.
Proof. exact (TRANS (@lem6961548 A B f) (@lem6961552 A)). Qed.
Lemma lem6961554 {A B : Type'} (f : type1415 A B) : (term92 A B f) = (True /\ True).
Proof. exact (MK_COMB (@lem6961219 A B f) (@lem6961553 A B f)). Qed.
Lemma lem6961556 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6961557 : (True /\ True) = True.
Proof. exact (@lem6961556 True). Qed.
Lemma lem6961558 {A B : Type'} (f : type1415 A B) : (term92 A B f) = True.
Proof. exact (TRANS (@lem6961554 A B f) (@lem6961557)). Qed.
Lemma lem6961559 {A B : Type'} (f : type1415 A B) : True = (term92 A B f).
Proof. exact (SYM (@lem6961558 A B f)). Qed.
Lemma lem6961560 {A B : Type'} (f : type1415 A B) : term92 A B f.
Proof. exact (EQ_MP (@lem6961559 A B f) (@lem0)). Qed.
Lemma lem6961561 {A B : Type'} (f : type1415 A B) : term64 A B f.
Proof. exact (@lem6961151 A B f (@lem6961560 A B f)). Qed.
Lemma lem6961562 {A B : Type'} (f : type1415 A B) : term63 A B f.
Proof. exact (EQ_MP (@lem6961118 A B f) (@lem6961561 A B f)). Qed.
Lemma lem6961567 {A B : Type'} : term237 A B.
Proof. exact (fun f : type1415 A B => @lem6961562 A B f). Qed.
