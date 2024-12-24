Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm6017756_term_abbrevs.
Require Import ITERATE_SUPERSET_spec.
Require Import SUBSET_spec.
Require Import support_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17265_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211724_spec.
Require Import thm3211725_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem6016893 {A B : Type'} (op : type1400 B) : term0 A B op.
Proof. exact (@lem6016892 A B op). Qed.
Lemma lem6016894 {A B : Type'} (op : type1400 B) : (term0 A B op) = (term1 A B op).
Proof. exact (eq_refl (term0 A B op)). Qed.
Lemma lem6016920 {_83095 : Type'} : term2 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem6016921 {_83095 : Type'} (p : _83095 -> Prop) : term3 _83095 p.
Proof. exact (@lem6016920 _83095 p). Qed.
Lemma lem6016922 {_83095 : Type'} (p : _83095 -> Prop) : (term3 _83095 p) = (term4 _83095 p).
Proof. exact (eq_refl (term3 _83095 p)). Qed.
Lemma lem6016923 {_83095 : Type'} (p : _83095 -> Prop) : term4 _83095 p.
Proof. exact (EQ_MP (@lem6016922 _83095 p) (@lem6016921 _83095 p)). Qed.
Lemma lem6016924 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term5 _83095 p x.
Proof. exact (@lem6016923 _83095 p x). Qed.
Lemma lem6016925 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term5 _83095 p x) = ((term6 _83095 x p) = (p x)).
Proof. exact (eq_refl (term5 _83095 p x)). Qed.
Lemma lem6016934 {A : Type'} (s : A -> Prop) : term7 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem6016935 {A : Type'} (s : A -> Prop) : (term7 A s) = (term8 A s).
Proof. exact (eq_refl (term7 A s)). Qed.
Lemma lem6016936 {A : Type'} (s : A -> Prop) : term8 A s.
Proof. exact (EQ_MP (@lem6016935 A s) (@lem6016934 A s)). Qed.
Lemma lem6016937 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term9 A s t.
Proof. exact (@lem6016936 A s t). Qed.
Lemma lem6016938 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term9 A s t) = ((@SUBSET A s t) = (term10 A s t)).
Proof. exact (eq_refl (term9 A s t)). Qed.
Lemma lem6016940 {A B : Type'} (s : A -> Prop) : term11 A B s.
Proof. exact (@lem5716761 A B s). Qed.
Lemma lem6016941 {A B : Type'} (s : A -> Prop) : (term11 A B s) = (term12 A B s).
Proof. exact (eq_refl (term11 A B s)). Qed.
Lemma lem6016942 {A B : Type'} (s : A -> Prop) : term12 A B s.
Proof. exact (EQ_MP (@lem6016941 A B s) (@lem6016940 A B s)). Qed.
Lemma lem6016943 {A B : Type'} (s : A -> Prop) (f : A -> B) : term13 A B s f.
Proof. exact (@lem6016942 A B s f). Qed.
Lemma lem6016944 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term13 A B s f) = (term14 A B s f).
Proof. exact (eq_refl (term13 A B s f)). Qed.
Lemma lem6016945 {A B : Type'} (s : A -> Prop) (f : A -> B) : term14 A B s f.
Proof. exact (EQ_MP (@lem6016944 A B s f) (@lem6016943 A B s f)). Qed.
Lemma lem6016946 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term15 A B s f op.
Proof. exact (@lem6016945 A B s f op). Qed.
Lemma lem6016947 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term15 A B s f op) = ((@support A B op f s) = (term16 A B s f op)).
Proof. exact (eq_refl (term15 A B s f op)). Qed.
Lemma lem6016966 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (EQ_MP (@lem6016938 A s t) (@lem6016937 A s t)). Qed.
Lemma lem6016967 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (@lem6016966 A s t). Qed.
Lemma lem6016968 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term17 A B op f s) = (term18 A B op f s).
Proof. exact (@lem6016967 A (@support A B op f (@UNIV A)) s). Qed.
Lemma lem6016976 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term16 A B s f op).
Proof. exact (EQ_MP (@lem6016947 A B s f op) (@lem6016946 A B s f op)). Qed.
Lemma lem6016977 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term16 A B s f op).
Proof. exact (@lem6016976 A B s f op). Qed.
Lemma lem6016978 {A B : Type'} (f : A -> B) (op : type1400 B) : (@support A B op f (@UNIV A)) = (term19 A B f op).
Proof. exact (@lem6016977 A B (@UNIV A) f op). Qed.
Lemma lem6016987 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6016988 {A B : Type'} (x : A) (f : A -> B) (op : type1400 B) : (term20 A B x op f) = (term21 A B x f op).
Proof. exact (MK_COMB (@lem6016987 A x) (@lem6016978 A B f op)). Qed.
Lemma lem6016990 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term6 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem6016925 _83095 p x) (@lem6016924 _83095 p x)). Qed.
Lemma lem6016991 {A : Type'} (p : A -> Prop) (x : A) : (term6 A x p) = (p x).
Proof. exact (@lem6016990 A p x). Qed.
Lemma lem6016992 {A B : Type'} (f : A -> B) (op : type1400 B) (x : A) : (term22 A B x f op) = (term23 A B f op x).
Proof. exact (@lem6016991 A (term24 A B f op) x). Qed.
Lemma lem6016993 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term23 A B f op x) = (term25 A B f x op).
Proof. exact (eq_refl (term23 A B f op x)). Qed.
Lemma lem6016994 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem6016995 {A B : Type'} (GEN_PVAR_237 : A) (f : A -> B) (x : A) (op : type1400 B) : (term26 A B GEN_PVAR_237 f op x) = (term27 A B GEN_PVAR_237 f x op).
Proof. exact (MK_COMB (@lem6016994 A GEN_PVAR_237) (@lem6016993 A B f x op)). Qed.
Lemma lem6016996 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6016997 {A B : Type'} (GEN_PVAR_237 : A) (f : A -> B) (op : type1400 B) (x : A) : (term28 A B GEN_PVAR_237 f op x) = (term29 A B GEN_PVAR_237 f op x).
Proof. exact (MK_COMB (@lem6016995 A B GEN_PVAR_237 f x op) (@lem6016996 A x)). Qed.
Lemma lem6016998 {A B : Type'} (GEN_PVAR_237 : A) (f : A -> B) (op : type1400 B) : (term30 A B GEN_PVAR_237 f op) = (term31 A B GEN_PVAR_237 f op).
Proof. exact (fun_ext (fun x : A => @lem6016997 A B GEN_PVAR_237 f op x)). Qed.
Lemma lem6016999 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6017000 {A B : Type'} (GEN_PVAR_237 : A) (f : A -> B) (op : type1400 B) : (term32 A B GEN_PVAR_237 f op) = (term33 A B GEN_PVAR_237 f op).
Proof. exact (MK_COMB (@lem6016999 A) (@lem6016998 A B GEN_PVAR_237 f op)). Qed.
Lemma lem6017001 {A B : Type'} (f : A -> B) (op : type1400 B) : (term34 A B f op) = (term35 A B f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem6017000 A B GEN_PVAR_237 f op)). Qed.
Lemma lem6017002 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6017003 {A B : Type'} (f : A -> B) (op : type1400 B) : (term36 A B f op) = (term19 A B f op).
Proof. exact (MK_COMB (@lem6017002 A) (@lem6017001 A B f op)). Qed.
Lemma lem6017004 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem6017005 {A B : Type'} (x : A) (f : A -> B) (op : type1400 B) : (term22 A B x f op) = (term21 A B x f op).
Proof. exact (MK_COMB (@lem6017004 A x) (@lem6017003 A B f op)). Qed.
Lemma lem6017006 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6017007 {A B : Type'} (x : A) (f : A -> B) (op : type1400 B) : (term37 A B x f op) = (term38 A B x f op).
Proof. exact (MK_COMB (@lem6017006) (@lem6017005 A B x f op)). Qed.
Lemma lem6017008 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term23 A B f op x) = (term25 A B f x op).
Proof. exact (eq_refl (term23 A B f op x)). Qed.
Lemma lem6017009 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : ((term22 A B x f op) = (term23 A B f op x)) = ((term21 A B x f op) = (term25 A B f x op)).
Proof. exact (MK_COMB (@lem6017007 A B x f op) (@lem6017008 A B f x op)). Qed.
Lemma lem6017010 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term21 A B x f op) = (term25 A B f x op).
Proof. exact (EQ_MP (@lem6017009 A B f x op) (@lem6016992 A B f op x)). Qed.
Lemma lem6017015 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term20 A B x op f) = (term25 A B f x op).
Proof. exact (TRANS (@lem6016988 A B x f op) (@lem6017010 A B f x op)). Qed.
Lemma lem6017016 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6017017 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term39 A B x op f) = (term40 A B f x op).
Proof. exact (MK_COMB (@lem6017016) (@lem6017015 A B f x op)). Qed.
Lemma lem6017018 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem6017019 {A B : Type'} (f : A -> B) (op : type1400 B) (x : A) (s : A -> Prop) : (term41 A B op f x s) = (term42 A B f op x s).
Proof. exact (MK_COMB (@lem6017017 A B f x op) (@lem6017018 A x s)). Qed.
Lemma lem6017022 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) : (term43 A B op f s) = (term44 A B f op s).
Proof. exact (fun_ext (fun x : A => @lem6017019 A B f op x s)). Qed.
Lemma lem6017023 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6017024 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) : (term18 A B op f s) = (term45 A B f op s).
Proof. exact (MK_COMB (@lem6017023 A) (@lem6017022 A B f op s)). Qed.
Lemma lem6017029 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) : (term17 A B op f s) = (term45 A B f op s).
Proof. exact (TRANS (@lem6016968 A B op f s) (@lem6017024 A B f op s)). Qed.
Lemma lem6017030 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6017031 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) : (term46 A B op f s) = (term47 A B f op s).
Proof. exact (MK_COMB (@lem6017030) (@lem6017029 A B f op s)). Qed.
Lemma lem6017034 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) : ((@iterate B A op s f) = (@iterate B A op (@UNIV A) f)) = ((@iterate B A op s f) = (@iterate B A op (@UNIV A) f)).
Proof. exact (eq_refl ((@iterate B A op s f) = (@iterate B A op (@UNIV A) f))). Qed.
Lemma lem6017035 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) : (term48 A B s op f) = (term49 A B s op f).
Proof. exact (MK_COMB (@lem6017031 A B f op s) (@lem6017034 A B s op f)). Qed.
Lemma lem6017038 {A B : Type'} (op : type1400 B) (f : A -> B) : (term50 A B op f) = (term51 A B op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6017035 A B s op f)). Qed.
Lemma lem6017039 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6017040 {A B : Type'} (op : type1400 B) (f : A -> B) : (term52 A B op f) = (term53 A B op f).
Proof. exact (MK_COMB (@lem6017039 A) (@lem6017038 A B op f)). Qed.
Lemma lem6017045 {A B : Type'} (op : type1400 B) : (term54 A B op) = (term55 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem6017040 A B op f)). Qed.
Lemma lem6017046 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem6017047 {A B : Type'} (op : type1400 B) : (term56 A B op) = (term57 A B op).
Proof. exact (MK_COMB (@lem6017046 A B) (@lem6017045 A B op)). Qed.
Lemma lem6017052 {B : Type'} (op : type1400 B) : (term58 B op) = (term58 B op).
Proof. exact (eq_refl (term58 B op)). Qed.
Lemma lem6017053 {A B : Type'} (op : type1400 B) : (term59 A B op) = (term60 A B op).
Proof. exact (MK_COMB (@lem6017052 B op) (@lem6017047 A B op)). Qed.
Lemma lem6017056 {A B : Type'} : (term61 A B) = (term62 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6017053 A B op)). Qed.
Lemma lem6017057 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6017058 {A B : Type'} : (term63 A B) = (term64 A B).
Proof. exact (MK_COMB (@lem6017057 B) (@lem6017056 A B)). Qed.
Lemma lem6017063 {A B : Type'} : (term64 A B) = (term63 A B).
Proof. exact (SYM (@lem6017058 A B)). Qed.
Lemma lem6017064 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem6017065 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (h1 : term45 A B f op s) : term45 A B f op s.
Proof. exact (h1). Qed.
Lemma lem6017066 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (h1 : (@iterate B A op s f) = (@iterate B A op (@UNIV A) f)) : (@iterate B A op s f) = (@iterate B A op (@UNIV A) f).
Proof. exact (h1). Qed.
Lemma lem6017067 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (h1 : (@iterate B A op s f) = (@iterate B A op (@UNIV A) f)) : (@iterate B A op (@UNIV A) f) = (@iterate B A op s f).
Proof. exact (SYM (@lem6017066 A B s op f h1)). Qed.
Lemma lem6017068 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : (@iterate B A op (@UNIV A) f) = (@iterate B A op s f)) : (@iterate B A op (@UNIV A) f) = (@iterate B A op s f).
Proof. exact (h1). Qed.
Lemma lem6017069 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (h1 : (@iterate B A op (@UNIV A) f) = (@iterate B A op s f)) : (@iterate B A op s f) = (@iterate B A op (@UNIV A) f).
Proof. exact (SYM (@lem6017068 A B op s f h1)). Qed.
Lemma lem6017070 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : ((@iterate B A op s f) = (@iterate B A op (@UNIV A) f)) = ((@iterate B A op (@UNIV A) f) = (@iterate B A op s f)).
Proof. exact (prop_ext (fun h1 : (@iterate B A op s f) = (@iterate B A op (@UNIV A) f) => @lem6017067 A B s op f h1) (fun h1 : (@iterate B A op (@UNIV A) f) = (@iterate B A op s f) => @lem6017069 A B op s f h1)). Qed.
Lemma lem6017071 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) : ((@iterate B A op (@UNIV A) f) = (@iterate B A op s f)) = ((@iterate B A op s f) = (@iterate B A op (@UNIV A) f)).
Proof. exact (SYM (@lem6017070 A B op s f)). Qed.
Lemma lem6017075 {A B : Type'} (op : type1400 B) : term1 A B op.
Proof. exact (EQ_MP (@lem6016894 A B op) (@lem6016893 A B op)). Qed.
Lemma lem6017076 {A B : Type'} (op : type1400 B) : term1 A B op.
Proof. exact (@lem6017075 A B op). Qed.
Lemma lem6017077 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term65 A B op.
Proof. exact (@lem6017076 A B op (@lem6017064 B op h1)). Qed.
Lemma lem6017078 {A B : Type'} (op : type1400 B) (h1 : term65 A B op) : term65 A B op.
Proof. exact (h1). Qed.
Lemma lem6017079 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : term65 A B op) : term66 A B op f.
Proof. exact (@lem6017078 A B op h1 f). Qed.
Lemma lem6017080 {A B : Type'} (op : type1400 B) (f : A -> B) : (term66 A B op f) = (term67 A B op f).
Proof. exact (eq_refl (term66 A B op f)). Qed.
Lemma lem6017081 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : term65 A B op) : term67 A B op f.
Proof. exact (EQ_MP (@lem6017080 A B op f) (@lem6017079 A B f op h1)). Qed.
Lemma lem6017082 {A B : Type'} (f : A -> B) (u : A -> Prop) (op : type1400 B) (h1 : term65 A B op) : term68 A B op f u.
Proof. exact (@lem6017081 A B f op h1 u). Qed.
Lemma lem6017083 {A B : Type'} (op : type1400 B) (u : A -> Prop) (f : A -> B) : (term68 A B op f u) = (term69 A B op u f).
Proof. exact (eq_refl (term68 A B op f u)). Qed.
Lemma lem6017084 {A B : Type'} (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term65 A B op) : term69 A B op u f.
Proof. exact (EQ_MP (@lem6017083 A B op u f) (@lem6017082 A B f u op h1)). Qed.
Lemma lem6017085 {A B : Type'} (u : A -> Prop) (f : A -> B) (v : A -> Prop) (op : type1400 B) (h1 : term65 A B op) : term70 A B op u f v.
Proof. exact (@lem6017084 A B u f op h1 v). Qed.
Lemma lem6017086 {A B : Type'} (v : A -> Prop) (op : type1400 B) (u : A -> Prop) (f : A -> B) : (term70 A B op u f v) = (term71 A B v op u f).
Proof. exact (eq_refl (term70 A B op u f v)). Qed.
Lemma lem6017087 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term65 A B op) : term71 A B v op u f.
Proof. exact (EQ_MP (@lem6017086 A B v op u f) (@lem6017085 A B u f v op h1)). Qed.
Lemma lem6017088 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term72 A B v u f op) : term72 A B v u f op.
Proof. exact (h1). Qed.
Lemma lem6017089 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term65 A B op) (h2 : term72 A B v u f op) : (@iterate B A op v f) = (@iterate B A op u f).
Proof. exact (@lem6017087 A B v u f op h1 (@lem6017088 A B v u f op h2)). Qed.
Lemma lem6017090 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term72 A B v u f op) : term73 A B v op u f.
Proof. exact (fun h0 : term65 A B op => @lem6017089 A B v u f op h0 h1). Qed.
Lemma lem6017091 {A B : Type'} (op : type1400 B) (h1 : term65 A B op) : term65 A B op.
Proof. exact (h1). Qed.
Lemma lem6017092 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term65 A B op) (h2 : term72 A B v u f op) : (@iterate B A op v f) = (@iterate B A op u f).
Proof. exact (@lem6017090 A B v u f op h2 (@lem6017091 A B op h1)). Qed.
Lemma lem6017093 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term65 A B op) : term71 A B v op u f.
Proof. exact (fun h0 : term72 A B v u f op => @lem6017092 A B v u f op h1 h0). Qed.
Lemma lem6017094 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (op : type1400 B) (h1 : term65 A B op) : term74 A B v op u.
Proof. exact (fun f : A -> B => @lem6017093 A B v u f op h1). Qed.
Lemma lem6017095 {A B : Type'} (v : A -> Prop) (op : type1400 B) (h1 : term65 A B op) : term75 A B v op.
Proof. exact (fun u : A -> Prop => @lem6017094 A B v u op h1). Qed.
Lemma lem6017096 {A B : Type'} (op : type1400 B) (h1 : term65 A B op) : term76 A B op.
Proof. exact (fun v : A -> Prop => @lem6017095 A B v op h1). Qed.
Lemma lem6017097 {A B : Type'} (op : type1400 B) : term77 A B op.
Proof. exact (fun h0 : term65 A B op => @lem6017096 A B op h0). Qed.
Lemma lem6017098 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term76 A B op.
Proof. exact (@lem6017097 A B op (@lem6017077 A B op h1)). Qed.
Lemma lem6017099 {A B : Type'} (v : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term78 A B op v.
Proof. exact (@lem6017098 A B op h1 v). Qed.
Lemma lem6017100 {A B : Type'} (v : A -> Prop) (op : type1400 B) : (term78 A B op v) = (term75 A B v op).
Proof. exact (eq_refl (term78 A B op v)). Qed.
Lemma lem6017101 {A B : Type'} (v : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term75 A B v op.
Proof. exact (EQ_MP (@lem6017100 A B v op) (@lem6017099 A B v op h1)). Qed.
Lemma lem6017102 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term79 A B v op u.
Proof. exact (@lem6017101 A B v op h1 u). Qed.
Lemma lem6017103 {A B : Type'} (v : A -> Prop) (op : type1400 B) (u : A -> Prop) : (term79 A B v op u) = (term74 A B v op u).
Proof. exact (eq_refl (term79 A B v op u)). Qed.
Lemma lem6017104 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term74 A B v op u.
Proof. exact (EQ_MP (@lem6017103 A B v op u) (@lem6017102 A B v u op h1)). Qed.
Lemma lem6017105 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term80 A B v op u f.
Proof. exact (@lem6017104 A B v u op h1 f). Qed.
Lemma lem6017106 {A B : Type'} (v : A -> Prop) (op : type1400 B) (u : A -> Prop) (f : A -> B) : (term80 A B v op u f) = (term71 A B v op u f).
Proof. exact (eq_refl (term80 A B v op u f)). Qed.
Lemma lem6017109 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term71 A B v op u f.
Proof. exact (EQ_MP (@lem6017106 A B v op u f) (@lem6017105 A B v u f op h1)). Qed.
Lemma lem6017110 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term71 A B v op u f.
Proof. exact (@lem6017109 A B v u f op h1). Qed.
Lemma lem6017111 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term81 A B op s f.
Proof. exact (@lem6017110 A B (@UNIV A) s f op h1). Qed.
Lemma lem6017139 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem6017140 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (@lem6017139 A s t). Qed.
Lemma lem6017141 {A : Type'} (s : A -> Prop) : (@SUBSET A s (@UNIV A)) = (term82 A s).
Proof. exact (@lem6017140 A s (@UNIV A)). Qed.
Lemma lem6017148 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6017149 {A : Type'} (s : A -> Prop) : (term83 A s) = (term84 A s).
Proof. exact (MK_COMB (@lem6017148) (@lem6017141 A s)). Qed.
Lemma lem6017162 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term85 A B s f op) = (term85 A B s f op).
Proof. exact (eq_refl (term85 A B s f op)). Qed.
Lemma lem6017163 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term86 A B s f op) = (term87 A B s f op).
Proof. exact (MK_COMB (@lem6017149 A s) (@lem6017162 A B s f op)). Qed.
Lemma lem6017166 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) : (term47 A B f op s) = (term47 A B f op s).
Proof. exact (eq_refl (term47 A B f op s)). Qed.
Lemma lem6017167 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term88 A B s f op) = (term89 A B s f op).
Proof. exact (MK_COMB (@lem6017166 A B f op s) (@lem6017163 A B s f op)). Qed.
Lemma lem6017170 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term89 A B s f op) = (term88 A B s f op).
Proof. exact (SYM (@lem6017167 A B s f op)). Qed.
Lemma lem6017182 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem6017183 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem6017182 A x). Qed.
Lemma lem6017184 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6017185 {A : Type'} (x : A) : (term90 A x) = (and True).
Proof. exact (MK_COMB (@lem6017184) (@lem6017183 A x)). Qed.
Lemma lem6017188 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term91 A B f x op) = (term91 A B f x op).
Proof. exact (eq_refl (term91 A B f x op)). Qed.
Lemma lem6017189 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term25 A B f x op) = (term92 A B f x op).
Proof. exact (MK_COMB (@lem6017185 A x) (@lem6017188 A B f x op)). Qed.
Lemma lem6017191 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6017192 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term92 A B f x op) = (term91 A B f x op).
Proof. exact (@lem6017191 (term91 A B f x op)). Qed.
Lemma lem6017195 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term25 A B f x op) = (term91 A B f x op).
Proof. exact (TRANS (@lem6017189 A B f x op) (@lem6017192 A B f x op)). Qed.
Lemma lem6017196 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6017197 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term40 A B f x op) = (term93 A B f x op).
Proof. exact (MK_COMB (@lem6017196) (@lem6017195 A B f x op)). Qed.
Lemma lem6017199 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6017200 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem6017199 A P x). Qed.
Lemma lem6017201 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem6017200 A s x). Qed.
Lemma lem6017202 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (x : A) : (term42 A B f op x s) = (term94 A B f op s x).
Proof. exact (MK_COMB (@lem6017197 A B f x op) (@lem6017201 A s x)). Qed.
Lemma lem6017205 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) : (term44 A B f op s) = (term95 A B f op s).
Proof. exact (fun_ext (fun x : A => @lem6017202 A B f op s x)). Qed.
Lemma lem6017206 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6017207 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) : (term45 A B f op s) = (term96 A B f op s).
Proof. exact (MK_COMB (@lem6017206 A) (@lem6017205 A B f op s)). Qed.
Lemma lem6017212 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6017213 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) : (term47 A B f op s) = (term97 A B f op s).
Proof. exact (MK_COMB (@lem6017212) (@lem6017207 A B f op s)). Qed.
Lemma lem6017223 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6017224 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem6017223 A P x). Qed.
Lemma lem6017225 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem6017224 A s x). Qed.
Lemma lem6017226 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6017227 {A : Type'} (s : A -> Prop) (x : A) : (term98 A x s) = (term99 A s x).
Proof. exact (MK_COMB (@lem6017226) (@lem6017225 A s x)). Qed.
Lemma lem6017229 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem6017230 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem6017229 A x). Qed.
Lemma lem6017231 {A : Type'} (s : A -> Prop) (x : A) : (term100 A s x) = (term101 A s x).
Proof. exact (MK_COMB (@lem6017227 A s x) (@lem6017230 A x)). Qed.
Lemma lem6017233 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6017234 {A : Type'} (s : A -> Prop) (x : A) : (term101 A s x) = True.
Proof. exact (@lem6017233 (s x)). Qed.
Lemma lem6017235 {A : Type'} (s : A -> Prop) (x : A) : (term100 A s x) = True.
Proof. exact (TRANS (@lem6017231 A s x) (@lem6017234 A s x)). Qed.
Lemma lem6017236 {A : Type'} (s : A -> Prop) : (term102 A s) = (term103 A).
Proof. exact (fun_ext (fun x : A => @lem6017235 A s x)). Qed.
Lemma lem6017237 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6017238 {A : Type'} (s : A -> Prop) : (term82 A s) = (term104 A).
Proof. exact (MK_COMB (@lem6017237 A) (@lem6017236 A s)). Qed.
Lemma lem6017240 {A : Type'} (t : Prop) : (term105 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6017241 {A : Type'} (t : Prop) : (term105 A t) = t.
Proof. exact (@lem6017240 A t). Qed.
Lemma lem6017242 {A : Type'} : (term104 A) = True.
Proof. exact (@lem6017241 A True). Qed.
Lemma lem6017243 {A : Type'} (s : A -> Prop) : (term82 A s) = True.
Proof. exact (TRANS (@lem6017238 A s) (@lem6017242 A)). Qed.
Lemma lem6017244 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6017245 {A : Type'} (s : A -> Prop) : (term84 A s) = (and True).
Proof. exact (MK_COMB (@lem6017244) (@lem6017243 A s)). Qed.
Lemma lem6017255 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem6017256 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem6017255 A x). Qed.
Lemma lem6017257 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6017258 {A : Type'} (x : A) : (term90 A x) = (and True).
Proof. exact (MK_COMB (@lem6017257) (@lem6017256 A x)). Qed.
Lemma lem6017260 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6017261 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem6017260 A P x). Qed.
Lemma lem6017262 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem6017261 A s x). Qed.
Lemma lem6017263 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6017264 {A : Type'} (s : A -> Prop) (x : A) : (term106 A x s) = (term107 A s x).
Proof. exact (MK_COMB (@lem6017263) (@lem6017262 A s x)). Qed.
Lemma lem6017265 {A : Type'} (s : A -> Prop) (x : A) : (term108 A x s) = (term109 A s x).
Proof. exact (MK_COMB (@lem6017258 A x) (@lem6017264 A s x)). Qed.
Lemma lem6017267 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6017268 {A : Type'} (s : A -> Prop) (x : A) : (term109 A s x) = (term107 A s x).
Proof. exact (@lem6017267 (term107 A s x)). Qed.
Lemma lem6017269 {A : Type'} (s : A -> Prop) (x : A) : (term108 A x s) = (term107 A s x).
Proof. exact (TRANS (@lem6017265 A s x) (@lem6017268 A s x)). Qed.
Lemma lem6017270 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6017271 {A : Type'} (s : A -> Prop) (x : A) : (term110 A x s) = (term111 A s x).
Proof. exact (MK_COMB (@lem6017270) (@lem6017269 A s x)). Qed.
Lemma lem6017274 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : ((f x) = (@neutral B op)) = ((f x) = (@neutral B op)).
Proof. exact (eq_refl ((f x) = (@neutral B op))). Qed.
Lemma lem6017275 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term112 A B s f x op) = (term113 A B s f x op).
Proof. exact (MK_COMB (@lem6017271 A s x) (@lem6017274 A B f x op)). Qed.
Lemma lem6017278 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term114 A B s f op) = (term115 A B s f op).
Proof. exact (fun_ext (fun x : A => @lem6017275 A B s f x op)). Qed.
Lemma lem6017279 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6017280 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term85 A B s f op) = (term116 A B s f op).
Proof. exact (MK_COMB (@lem6017279 A) (@lem6017278 A B s f op)). Qed.
Lemma lem6017285 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term87 A B s f op) = (term117 A B s f op).
Proof. exact (MK_COMB (@lem6017245 A s) (@lem6017280 A B s f op)). Qed.
Lemma lem6017287 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6017288 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term117 A B s f op) = (term116 A B s f op).
Proof. exact (@lem6017287 (term116 A B s f op)). Qed.
Lemma lem6017297 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term87 A B s f op) = (term116 A B s f op).
Proof. exact (TRANS (@lem6017285 A B s f op) (@lem6017288 A B s f op)). Qed.
Lemma lem6017298 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term89 A B s f op) = (term118 A B s f op).
Proof. exact (MK_COMB (@lem6017213 A B f op s) (@lem6017297 A B s f op)). Qed.
Lemma lem6017301 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term118 A B s f op) = (term89 A B s f op).
Proof. exact (SYM (@lem6017298 A B s f op)). Qed.
Lemma lem6017303 (p : Prop) : p = (term119 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6017304 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term118 A B s f op) = (term120 A B s f op).
Proof. exact (@lem6017303 (term118 A B s f op)). Qed.
Lemma lem6017305 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term120 A B s f op) = (term118 A B s f op).
Proof. exact (SYM (@lem6017304 A B s f op)). Qed.
Lemma lem6017306 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term121 A B s f op) : term121 A B s f op.
Proof. exact (h1). Qed.
Lemma lem6017309 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term120 A B s f op) : term120 A B s f op.
Proof. exact (h1). Qed.
Lemma lem6017310 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term122 A B s f op.
Proof. exact (fun h0 : term120 A B s f op => @lem6017309 A B s f op h0). Qed.
Lemma lem6017311 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term122 A B s f op) : term122 A B s f op.
Proof. exact (h1). Qed.
Lemma lem6017312 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term120 A B s f op) : term120 A B s f op.
Proof. exact (h1). Qed.
Lemma lem6017313 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term120 A B s f op) (h2 : term122 A B s f op) : term120 A B s f op.
Proof. exact (@lem6017311 A B s f op h2 (@lem6017312 A B s f op h1)). Qed.
Lemma lem6017314 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term120 A B s f op) : term123 A B s f op.
Proof. exact (fun h0 : term122 A B s f op => @lem6017313 A B s f op h1 h0). Qed.
Lemma lem6017315 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term122 A B s f op) : term122 A B s f op.
Proof. exact (h1). Qed.
Lemma lem6017316 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term120 A B s f op) (h2 : term122 A B s f op) : term120 A B s f op.
Proof. exact (@lem6017314 A B s f op h1 (@lem6017315 A B s f op h2)). Qed.
Lemma lem6017317 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term122 A B s f op) : term122 A B s f op.
Proof. exact (fun h0 : term120 A B s f op => @lem6017316 A B s f op h0 h1). Qed.
Lemma lem6017318 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term124 A B s f op.
Proof. exact (fun h0 : term122 A B s f op => @lem6017317 A B s f op h0). Qed.
Lemma lem6017321 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term122 A B s f op.
Proof. exact (@lem6017318 A B s f op (@lem6017310 A B s f op)). Qed.
Lemma lem6017322 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term122 A B s f op.
Proof. exact (@lem6017321 A B s f op). Qed.
Lemma lem6017336 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6017337 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term120 A B s f op) = (term125 A B s f op).
Proof. exact (@lem6017336 (term121 A B s f op)). Qed.
Lemma lem6017339 (t : Prop) : (term126 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6017340 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term125 A B s f op) = (term118 A B s f op).
Proof. exact (@lem6017339 (term118 A B s f op)). Qed.
Lemma lem6017343 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term120 A B s f op) = (term118 A B s f op).
Proof. exact (TRANS (@lem6017337 A B s f op) (@lem6017340 A B s f op)). Qed.
Lemma lem6017356 {A B : Type'} (f : A -> B) (op : type1400 B) : (term127 A B f op) = (term128 A B f op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6017343 A B s f op)). Qed.
Lemma lem6017357 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6017358 {A B : Type'} (f : A -> B) (op : type1400 B) : (term129 A B f op) = (term130 A B f op).
Proof. exact (MK_COMB (@lem6017357 A) (@lem6017356 A B f op)). Qed.
Lemma lem6017363 {A B : Type'} (op : type1400 B) : (term131 A B op) = (term132 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem6017358 A B f op)). Qed.
Lemma lem6017364 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem6017365 {A B : Type'} (op : type1400 B) : (term133 A B op) = (term134 A B op).
Proof. exact (MK_COMB (@lem6017364 A B) (@lem6017363 A B op)). Qed.
Lemma lem6017370 {A B : Type'} : (term135 A B) = (term136 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6017365 A B op)). Qed.
Lemma lem6017371 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6017380 {A B : Type'} : (term137 A B) = (term138 A B).
Proof. exact (MK_COMB (@lem6017371 B) (@lem6017370 A B)). Qed.
Lemma lem6017387 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term113 A B s f x op) = (term113 A B s f x op).
Proof. exact (eq_refl (term113 A B s f x op)). Qed.
Lemma lem6017388 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term115 A B s f op) = (term115 A B s f op).
Proof. exact (fun_ext (fun x : A => @lem6017387 A B s f x op)). Qed.
Lemma lem6017389 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6017390 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term116 A B s f op) = (term116 A B s f op).
Proof. exact (MK_COMB (@lem6017389 A) (@lem6017388 A B s f op)). Qed.
Lemma lem6017397 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (x : A) : (term94 A B f op s x) = (term94 A B f op s x).
Proof. exact (eq_refl (term94 A B f op s x)). Qed.
Lemma lem6017398 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) : (term95 A B f op s) = (term95 A B f op s).
Proof. exact (fun_ext (fun x : A => @lem6017397 A B f op s x)). Qed.
Lemma lem6017399 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6017400 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) : (term96 A B f op s) = (term96 A B f op s).
Proof. exact (MK_COMB (@lem6017399 A) (@lem6017398 A B f op s)). Qed.
Lemma lem6017401 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6017402 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) : (term97 A B f op s) = (term97 A B f op s).
Proof. exact (MK_COMB (@lem6017401) (@lem6017400 A B f op s)). Qed.
Lemma lem6017403 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term118 A B s f op) = (term118 A B s f op).
Proof. exact (MK_COMB (@lem6017402 A B f op s) (@lem6017390 A B s f op)). Qed.
Lemma lem6017404 {A B : Type'} (f : A -> B) (op : type1400 B) : (term128 A B f op) = (term128 A B f op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6017403 A B s f op)). Qed.
Lemma lem6017405 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6017406 {A B : Type'} (f : A -> B) (op : type1400 B) : (term130 A B f op) = (term130 A B f op).
Proof. exact (MK_COMB (@lem6017405 A) (@lem6017404 A B f op)). Qed.
Lemma lem6017407 {A B : Type'} (op : type1400 B) : (term132 A B op) = (term132 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem6017406 A B f op)). Qed.
Lemma lem6017408 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem6017409 {A B : Type'} (op : type1400 B) : (term134 A B op) = (term134 A B op).
Proof. exact (MK_COMB (@lem6017408 A B) (@lem6017407 A B op)). Qed.
Lemma lem6017410 {A B : Type'} : (term136 A B) = (term136 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6017409 A B op)). Qed.
Lemma lem6017411 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6017412 {A B : Type'} : (term138 A B) = (term138 A B).
Proof. exact (MK_COMB (@lem6017411 B) (@lem6017410 A B)). Qed.
Lemma lem6017451 {A B : Type'} : (term137 A B) = (term138 A B).
Proof. exact (TRANS (@lem6017380 A B) (@lem6017412 A B)). Qed.
Lemma lem6017452 {A B : Type'} : (term138 A B) = (term137 A B).
Proof. exact (SYM (@lem6017451 A B)). Qed.
Lemma lem6017453 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (h1 : term96 A B f op s) : term96 A B f op s.
Proof. exact (h1). Qed.
Lemma lem6017456 (p : Prop) : p = (term119 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6017457 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : ((f x) = (@neutral B op)) = (term139 A B f x op).
Proof. exact (@lem6017456 ((f x) = (@neutral B op))). Qed.
Lemma lem6017458 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term139 A B f x op) = ((f x) = (@neutral B op)).
Proof. exact (SYM (@lem6017457 A B f x op)). Qed.
Lemma lem6017459 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (h1 : term91 A B f x op) : term91 A B f x op.
Proof. exact (h1). Qed.
Lemma lem6017462 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term140 A B f x op) = ((f x) = (@neutral B op)).
Proof. exact (@lem16933 ((f x) = (@neutral B op))). Qed.
Lemma lem6017463 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem6017464 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6017465 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term141 A B f x op) = (term142 A B f x op).
Proof. exact (MK_COMB (@lem6017464) (@lem6017462 A B f x op)). Qed.
Lemma lem6017466 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (x : A) : (term143 A B f op s x) = (term144 A B f op s x).
Proof. exact (MK_COMB (@lem6017465 A B f x op) (@lem6017463 A s x)). Qed.
Lemma lem6017467 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (x : A) : (term94 A B f op s x) = (term143 A B f op s x).
Proof. exact (@lem17265 (term91 A B f x op) (s x)). Qed.
Lemma lem6017468 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (x : A) : (term94 A B f op s x) = (term144 A B f op s x).
Proof. exact (TRANS (@lem6017467 A B f op s x) (@lem6017466 A B f op s x)). Qed.
Lemma lem6017469 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) : (term95 A B f op s) = (term145 A B f op s).
Proof. exact (fun_ext (fun x : A => @lem6017468 A B f op s x)). Qed.
Lemma lem6017470 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6017507 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) : (term96 A B f op s) = (term146 A B f op s).
Proof. exact (MK_COMB (@lem6017470 A) (@lem6017469 A B f op s)). Qed.
Lemma lem6017508 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (h1 : term96 A B f op s) : term146 A B f op s.
Proof. exact (EQ_MP (@lem6017507 A B f op s) (@lem6017453 A B f op s h1)). Qed.
Lemma lem6017514 {A : Type'} (s : A -> Prop) (x : A) (h1 : term107 A s x) : term107 A s x.
Proof. exact (h1). Qed.
Lemma lem6017520 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (h1 : term91 A B f x op) : term91 A B f x op.
Proof. exact (h1). Qed.
Lemma lem6017535 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (x : A) : (term144 A B f op s x) = (term144 A B f op s x).
Proof. exact (eq_refl (term144 A B f op s x)). Qed.
Lemma lem6017536 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) : (term145 A B f op s) = (term145 A B f op s).
Proof. exact (fun_ext (fun x : A => @lem6017535 A B f op s x)). Qed.
Lemma lem6017537 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6017538 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) : (term146 A B f op s) = (term146 A B f op s).
Proof. exact (MK_COMB (@lem6017537 A) (@lem6017536 A B f op s)). Qed.
Lemma lem6017539 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (h1 : term96 A B f op s) : term146 A B f op s.
Proof. exact (EQ_MP (@lem6017538 A B f op s) (@lem6017508 A B f op s h1)). Qed.
Lemma lem6017545 {A : Type'} (s : A -> Prop) (x : A) (h1 : term107 A s x) : term107 A s x.
Proof. exact (h1). Qed.
Lemma lem6017557 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (h1 : term91 A B f x op) : term91 A B f x op.
Proof. exact (h1). Qed.
Lemma lem6017565 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (x : A) : (term144 A B f op s x) = (term144 A B f op s x).
Proof. exact (eq_refl (term144 A B f op s x)). Qed.
Lemma lem6017566 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) : (term145 A B f op s) = (term145 A B f op s).
Proof. exact (fun_ext (fun x : A => @lem6017565 A B f op s x)). Qed.
Lemma lem6017567 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6017569 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) : (term146 A B f op s) = (term146 A B f op s).
Proof. exact (MK_COMB (@lem6017567 A) (@lem6017566 A B f op s)). Qed.
Lemma lem6017570 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (h1 : term96 A B f op s) : term146 A B f op s.
Proof. exact (EQ_MP (@lem6017569 A B f op s) (@lem6017539 A B f op s h1)). Qed.
Lemma lem6017574 {A : Type'} (s : A -> Prop) (x : A) (h1 : term107 A s x) : term107 A s x.
Proof. exact (h1). Qed.
Lemma lem6017578 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (h1 : term91 A B f x op) : term91 A B f x op.
Proof. exact (h1). Qed.
Lemma lem6017579 {A B : Type'} (_76739 : A) (f : A -> B) (op : type1400 B) (s : A -> Prop) (h1 : term96 A B f op s) : term147 A B f op s _76739.
Proof. exact (@lem6017570 A B f op s h1 _76739). Qed.
Lemma lem6017580 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (_76739 : A) : (term147 A B f op s _76739) = (term144 A B f op s _76739).
Proof. exact (eq_refl (term147 A B f op s _76739)). Qed.
Lemma lem6017587 {A B : Type'} (_76739 : A) (f : A -> B) (op : type1400 B) (s : A -> Prop) (h1 : term96 A B f op s) : term144 A B f op s _76739.
Proof. exact (EQ_MP (@lem6017580 A B f op s _76739) (@lem6017579 A B _76739 f op s h1)). Qed.
Lemma lem6017589 {A : Type'} (s : A -> Prop) (x : A) (h1 : term107 A s x) : term107 A s x.
Proof. exact (h1). Qed.
Lemma lem6017591 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (h1 : term91 A B f x op) : term91 A B f x op.
Proof. exact (h1). Qed.
Lemma lem6017627 {A : Type'} (s : A -> Prop) (x : A) (h1 : term107 A s x) : term107 A s x.
Proof. exact (h1). Qed.
Lemma lem6017628 {A : Type'} (s : A -> Prop) (x : A) (h1 : term107 A s x) : term148 A s x.
Proof. exact (fun h0 : s x => @lem6017627 A s x h1). Qed.
Lemma lem6017630 (p : Prop) : (term149 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6017631 {A : Type'} (s : A -> Prop) (x : A) : (term148 A s x) = (term107 A s x).
Proof. exact (@lem6017630 (s x)). Qed.
Lemma lem6017632 {A : Type'} (s : A -> Prop) (x : A) (h1 : term107 A s x) : term107 A s x.
Proof. exact (EQ_MP (@lem6017631 A s x) (@lem6017628 A s x h1)). Qed.
Lemma lem6017634 (b : Prop) (a : Prop) : (a \/ b) = (term150 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6017637 {A B : Type'} (s : A -> Prop) (f : A -> B) (_76739 : A) (op : type1400 B) : (term144 A B f op s _76739) = (term113 A B s f _76739 op).
Proof. exact (@lem6017634 (s _76739) ((f _76739) = (@neutral B op))). Qed.
Lemma lem6017640 {A B : Type'} (_76739 : A) (f : A -> B) (op : type1400 B) (s : A -> Prop) (h1 : term96 A B f op s) : term113 A B s f _76739 op.
Proof. exact (EQ_MP (@lem6017637 A B s f _76739 op) (@lem6017587 A B _76739 f op s h1)). Qed.
Lemma lem6017641 {A B : Type'} (_76739 : A) (f : A -> B) (op : type1400 B) (s : A -> Prop) (h1 : term96 A B f op s) : term113 A B s f _76739 op.
Proof. exact (@lem6017640 A B _76739 f op s h1). Qed.
Lemma lem6017642 {A B : Type'} (x : A) (f : A -> B) (op : type1400 B) (s : A -> Prop) (h1 : term96 A B f op s) : term113 A B s f x op.
Proof. exact (@lem6017641 A B x f op s h1). Qed.
Lemma lem6017645 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (x : A) (h1 : term96 A B f op s) (h2 : term107 A s x) : (f x) = (@neutral B op).
Proof. exact (@lem6017642 A B x f op s h1 (@lem6017632 A s x h2)). Qed.
Lemma lem6017646 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (x : A) (h1 : term96 A B f op s) (h2 : term107 A s x) : term151 A B f x op.
Proof. exact (fun h0 : term91 A B f x op => @lem6017645 A B f op s x h1 h2). Qed.
Lemma lem6017648 (p : Prop) : (term152 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6017649 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term151 A B f x op) = ((f x) = (@neutral B op)).
Proof. exact (@lem6017648 ((f x) = (@neutral B op))). Qed.
Lemma lem6017650 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (x : A) (h1 : term96 A B f op s) (h2 : term107 A s x) : (f x) = (@neutral B op).
Proof. exact (EQ_MP (@lem6017649 A B f x op) (@lem6017646 A B f op s x h1 h2)). Qed.
Lemma lem6017653 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6017655 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term91 A B f x op) = (term153 A B f x op).
Proof. exact (@lem6017653 ((f x) = (@neutral B op))). Qed.
Lemma lem6017658 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (h1 : term91 A B f x op) : term153 A B f x op.
Proof. exact (EQ_MP (@lem6017655 A B f x op) (@lem6017591 A B f x op h1)). Qed.
Lemma lem6017661 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term96 A B f op s) (h2 : term107 A s x) (h3 : term91 A B f x op) : False.
Proof. exact (@lem6017658 A B f x op h3 (@lem6017650 A B f op s x h1 h2)). Qed.
Lemma lem6017662 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term96 A B f op s) (h2 : term107 A s x) (h3 : term91 A B f x op) : term154.
Proof. exact (fun h0 : ~ False => @lem6017661 A B s f x op h1 h2 h3). Qed.
Lemma lem6017664 (p : Prop) : (term152 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6017665 : term154 = False.
Proof. exact (@lem6017664 False). Qed.
Lemma lem6017666 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term96 A B f op s) (h2 : term107 A s x) (h3 : term91 A B f x op) : False.
Proof. exact (EQ_MP (@lem6017665) (@lem6017662 A B s f x op h1 h2 h3)). Qed.
Lemma lem6017667 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term96 A B f op s) (h2 : term107 A s x) (h3 : term91 A B f x op) : (term91 A B f x op) = False.
Proof. exact (prop_ext (fun h4 : term91 A B f x op => @lem6017666 A B s f x op h1 h2 h3) (fun h4 : False => @lem6017591 A B f x op h3)). Qed.
Lemma lem6017668 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term96 A B f op s) (h2 : term107 A s x) (h3 : term91 A B f x op) : False.
Proof. exact (EQ_MP (@lem6017667 A B s f x op h1 h2 h3) (@lem6017591 A B f x op h3)). Qed.
Lemma lem6017669 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term96 A B f op s) (h2 : term107 A s x) (h3 : term91 A B f x op) : (term107 A s x) = False.
Proof. exact (prop_ext (fun h4 : term107 A s x => @lem6017668 A B s f x op h1 h2 h3) (fun h4 : False => @lem6017589 A s x h2)). Qed.
Lemma lem6017670 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term96 A B f op s) (h2 : term107 A s x) (h3 : term91 A B f x op) : False.
Proof. exact (EQ_MP (@lem6017669 A B s f x op h1 h2 h3) (@lem6017589 A s x h2)). Qed.
Lemma lem6017671 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term96 A B f op s) (h2 : term107 A s x) (h3 : term91 A B f x op) : (term91 A B f x op) = False.
Proof. exact (prop_ext (fun h4 : term91 A B f x op => @lem6017670 A B s f x op h1 h2 h3) (fun h4 : False => @lem6017578 A B f x op h3)). Qed.
Lemma lem6017672 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term96 A B f op s) (h2 : term107 A s x) (h3 : term91 A B f x op) : False.
Proof. exact (EQ_MP (@lem6017671 A B s f x op h1 h2 h3) (@lem6017578 A B f x op h3)). Qed.
Lemma lem6017673 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term96 A B f op s) (h2 : term107 A s x) (h3 : term91 A B f x op) : (term107 A s x) = False.
Proof. exact (prop_ext (fun h4 : term107 A s x => @lem6017672 A B s f x op h1 h2 h3) (fun h4 : False => @lem6017574 A s x h2)). Qed.
Lemma lem6017674 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term96 A B f op s) (h2 : term107 A s x) (h3 : term91 A B f x op) : False.
Proof. exact (EQ_MP (@lem6017673 A B s f x op h1 h2 h3) (@lem6017574 A s x h2)). Qed.
Lemma lem6017675 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term96 A B f op s) (h2 : term107 A s x) (h3 : term91 A B f x op) : (term91 A B f x op) = False.
Proof. exact (prop_ext (fun h4 : term91 A B f x op => @lem6017674 A B s f x op h1 h2 h3) (fun h4 : False => @lem6017578 A B f x op h3)). Qed.
Lemma lem6017676 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term96 A B f op s) (h2 : term107 A s x) (h3 : term91 A B f x op) : False.
Proof. exact (EQ_MP (@lem6017675 A B s f x op h1 h2 h3) (@lem6017578 A B f x op h3)). Qed.
Lemma lem6017677 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term96 A B f op s) (h2 : term107 A s x) (h3 : term91 A B f x op) : (term107 A s x) = False.
Proof. exact (prop_ext (fun h4 : term107 A s x => @lem6017676 A B s f x op h1 h2 h3) (fun h4 : False => @lem6017574 A s x h2)). Qed.
Lemma lem6017678 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term96 A B f op s) (h2 : term107 A s x) (h3 : term91 A B f x op) : False.
Proof. exact (EQ_MP (@lem6017677 A B s f x op h1 h2 h3) (@lem6017574 A s x h2)). Qed.
Lemma lem6017679 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term96 A B f op s) (h2 : term107 A s x) (h3 : term91 A B f x op) : (term91 A B f x op) = False.
Proof. exact (prop_ext (fun h4 : term91 A B f x op => @lem6017678 A B s f x op h1 h2 h3) (fun h4 : False => @lem6017557 A B f x op h3)). Qed.
Lemma lem6017680 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term96 A B f op s) (h2 : term107 A s x) (h3 : term91 A B f x op) : False.
Proof. exact (EQ_MP (@lem6017679 A B s f x op h1 h2 h3) (@lem6017557 A B f x op h3)). Qed.
Lemma lem6017681 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term96 A B f op s) (h2 : term107 A s x) (h3 : term91 A B f x op) : (term107 A s x) = False.
Proof. exact (prop_ext (fun h4 : term107 A s x => @lem6017680 A B s f x op h1 h2 h3) (fun h4 : False => @lem6017545 A s x h2)). Qed.
Lemma lem6017682 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term96 A B f op s) (h2 : term107 A s x) (h3 : term91 A B f x op) : False.
Proof. exact (EQ_MP (@lem6017681 A B s f x op h1 h2 h3) (@lem6017545 A s x h2)). Qed.
Lemma lem6017683 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term96 A B f op s) (h2 : term107 A s x) (h3 : term91 A B f x op) : (term91 A B f x op) = False.
Proof. exact (prop_ext (fun h4 : term91 A B f x op => @lem6017682 A B s f x op h1 h2 h3) (fun h4 : False => @lem6017520 A B f x op h3)). Qed.
Lemma lem6017684 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term96 A B f op s) (h2 : term107 A s x) (h3 : term91 A B f x op) : False.
Proof. exact (EQ_MP (@lem6017683 A B s f x op h1 h2 h3) (@lem6017520 A B f x op h3)). Qed.
Lemma lem6017685 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term96 A B f op s) (h2 : term107 A s x) (h3 : term91 A B f x op) : (term107 A s x) = False.
Proof. exact (prop_ext (fun h4 : term107 A s x => @lem6017684 A B s f x op h1 h2 h3) (fun h4 : False => @lem6017514 A s x h2)). Qed.
Lemma lem6017686 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term96 A B f op s) (h2 : term107 A s x) (h3 : term91 A B f x op) : False.
Proof. exact (EQ_MP (@lem6017685 A B s f x op h1 h2 h3) (@lem6017514 A s x h2)). Qed.
Lemma lem6017687 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term96 A B f op s) (h2 : term107 A s x) (h3 : term91 A B f x op) : (term91 A B f x op) = False.
Proof. exact (prop_ext (fun h4 : term91 A B f x op => @lem6017686 A B s f x op h1 h2 h3) (fun h4 : False => @lem6017459 A B f x op h3)). Qed.
Lemma lem6017688 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term96 A B f op s) (h2 : term107 A s x) (h3 : term91 A B f x op) : False.
Proof. exact (EQ_MP (@lem6017687 A B s f x op h1 h2 h3) (@lem6017459 A B f x op h3)). Qed.
Lemma lem6017689 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (x : A) (h1 : term96 A B f op s) (h2 : term107 A s x) : term139 A B f x op.
Proof. exact (fun h0 : term91 A B f x op => @lem6017688 A B s f x op h1 h2 h0). Qed.
Lemma lem6017690 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (x : A) (h1 : term96 A B f op s) (h2 : term107 A s x) : (f x) = (@neutral B op).
Proof. exact (EQ_MP (@lem6017458 A B f x op) (@lem6017689 A B f op s x h1 h2)). Qed.
Lemma lem6017691 {A B : Type'} (x : A) (f : A -> B) (op : type1400 B) (s : A -> Prop) (h1 : term96 A B f op s) : term113 A B s f x op.
Proof. exact (fun h0 : term107 A s x => @lem6017690 A B f op s x h1 h0). Qed.
Lemma lem6017696 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (h1 : term96 A B f op s) : term116 A B s f op.
Proof. exact (fun x : A => @lem6017691 A B x f op s h1). Qed.
Lemma lem6017697 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term118 A B s f op.
Proof. exact (fun h0 : term96 A B f op s => @lem6017696 A B f op s h0). Qed.
Lemma lem6017702 {A B : Type'} (f : A -> B) (op : type1400 B) : term130 A B f op.
Proof. exact (fun s : A -> Prop => @lem6017697 A B s f op). Qed.
Lemma lem6017707 {A B : Type'} (op : type1400 B) : term134 A B op.
Proof. exact (fun f : A -> B => @lem6017702 A B f op). Qed.
Lemma lem6017712 {A B : Type'} : term138 A B.
Proof. exact (fun op : type1400 B => @lem6017707 A B op). Qed.
Lemma lem6017713 {A B : Type'} : term137 A B.
Proof. exact (EQ_MP (@lem6017452 A B) (@lem6017712 A B)). Qed.
Lemma lem6017714 {A B : Type'} (op : type1400 B) : term155 A B op.
Proof. exact (@lem6017713 A B op). Qed.
Lemma lem6017715 {A B : Type'} (op : type1400 B) : (term155 A B op) = (term133 A B op).
Proof. exact (eq_refl (term155 A B op)). Qed.
Lemma lem6017716 {A B : Type'} (op : type1400 B) : term133 A B op.
Proof. exact (EQ_MP (@lem6017715 A B op) (@lem6017714 A B op)). Qed.
Lemma lem6017717 {A B : Type'} (op : type1400 B) (f : A -> B) : term156 A B op f.
Proof. exact (@lem6017716 A B op f). Qed.
Lemma lem6017718 {A B : Type'} (f : A -> B) (op : type1400 B) : (term156 A B op f) = (term129 A B f op).
Proof. exact (eq_refl (term156 A B op f)). Qed.
Lemma lem6017719 {A B : Type'} (f : A -> B) (op : type1400 B) : term129 A B f op.
Proof. exact (EQ_MP (@lem6017718 A B f op) (@lem6017717 A B op f)). Qed.
Lemma lem6017720 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) : term157 A B f op s.
Proof. exact (@lem6017719 A B f op s). Qed.
Lemma lem6017721 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term157 A B f op s) = (term120 A B s f op).
Proof. exact (eq_refl (term157 A B f op s)). Qed.
Lemma lem6017722 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term120 A B s f op.
Proof. exact (EQ_MP (@lem6017721 A B s f op) (@lem6017720 A B f op s)). Qed.
Lemma lem6017724 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term120 A B s f op.
Proof. exact (@lem6017322 A B s f op (@lem6017722 A B s f op)). Qed.
Lemma lem6017725 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term121 A B s f op) : False.
Proof. exact (@lem6017724 A B s f op (@lem6017306 A B s f op h1)). Qed.
Lemma lem6017726 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term121 A B s f op) : (term121 A B s f op) = False.
Proof. exact (prop_ext (fun h2 : term121 A B s f op => @lem6017725 A B s f op h1) (fun h2 : False => @lem6017306 A B s f op h1)). Qed.
Lemma lem6017727 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term121 A B s f op) : False.
Proof. exact (EQ_MP (@lem6017726 A B s f op h1) (@lem6017306 A B s f op h1)). Qed.
Lemma lem6017728 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term120 A B s f op.
Proof. exact (fun h0 : term121 A B s f op => @lem6017727 A B s f op h0). Qed.
Lemma lem6017729 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term118 A B s f op.
Proof. exact (EQ_MP (@lem6017305 A B s f op) (@lem6017728 A B s f op)). Qed.
Lemma lem6017730 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term89 A B s f op.
Proof. exact (EQ_MP (@lem6017301 A B s f op) (@lem6017729 A B s f op)). Qed.
Lemma lem6017731 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term88 A B s f op.
Proof. exact (EQ_MP (@lem6017170 A B s f op) (@lem6017730 A B s f op)). Qed.
Lemma lem6017732 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (h1 : term45 A B f op s) : term86 A B s f op.
Proof. exact (@lem6017731 A B s f op (@lem6017065 A B f op s h1)). Qed.
Lemma lem6017733 {A B : Type'} (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term45 A B f op s) (h2 : @monoidal B op) : (@iterate B A op (@UNIV A) f) = (@iterate B A op s f).
Proof. exact (@lem6017111 A B s f op h2 (@lem6017732 A B f op s h1)). Qed.
Lemma lem6017734 {A B : Type'} (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term45 A B f op s) (h2 : @monoidal B op) : (@iterate B A op s f) = (@iterate B A op (@UNIV A) f).
Proof. exact (EQ_MP (@lem6017071 A B s op f) (@lem6017733 A B f s op h1 h2)). Qed.
Lemma lem6017735 {A B : Type'} (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term45 A B f op s) (h2 : @monoidal B op) : (term45 A B f op s) = ((@iterate B A op s f) = (@iterate B A op (@UNIV A) f)).
Proof. exact (prop_ext (fun h3 : term45 A B f op s => @lem6017734 A B f s op h1 h2) (fun h3 : (@iterate B A op s f) = (@iterate B A op (@UNIV A) f) => @lem6017065 A B f op s h1)). Qed.
Lemma lem6017736 {A B : Type'} (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term45 A B f op s) (h2 : @monoidal B op) : (@iterate B A op s f) = (@iterate B A op (@UNIV A) f).
Proof. exact (EQ_MP (@lem6017735 A B f s op h1 h2) (@lem6017065 A B f op s h1)). Qed.
Lemma lem6017737 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term49 A B s op f.
Proof. exact (fun h0 : term45 A B f op s => @lem6017736 A B f s op h0 h1). Qed.
Lemma lem6017742 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term53 A B op f.
Proof. exact (fun s : A -> Prop => @lem6017737 A B s f op h1). Qed.
Lemma lem6017747 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term57 A B op.
Proof. exact (fun f : A -> B => @lem6017742 A B f op h1). Qed.
Lemma lem6017748 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = (term57 A B op).
Proof. exact (prop_ext (fun h2 : @monoidal B op => @lem6017747 A B op h1) (fun h2 : term57 A B op => @lem6017064 B op h1)). Qed.
Lemma lem6017749 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term57 A B op.
Proof. exact (EQ_MP (@lem6017748 A B op h1) (@lem6017064 B op h1)). Qed.
Lemma lem6017750 {A B : Type'} (op : type1400 B) : term60 A B op.
Proof. exact (fun h0 : @monoidal B op => @lem6017749 A B op h0). Qed.
Lemma lem6017755 {A B : Type'} : term64 A B.
Proof. exact (fun op : type1400 B => @lem6017750 A B op). Qed.
Lemma lem6017756 {A B : Type'} : term63 A B.
Proof. exact (EQ_MP (@lem6017063 A B) (@lem6017755 A B)). Qed.
