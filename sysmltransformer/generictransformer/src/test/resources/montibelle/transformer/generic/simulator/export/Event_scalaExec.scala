object StreamEqual {
  def streamequal[A](a:Any,b:Any): Boolean = a==b
}

object Event_scalaExec {

trait below[A] {
  val `Event_scalaExec.below` : (A, A) => Boolean
}
def below[A](a : A, b : A)(implicit A: below[A]) : Boolean =
  A.`Event_scalaExec.below`(a, b)
object below {
  implicit def
    `Event_scalaExec.below_combinedstream`[A : countable : equal] : below[combinedstream[A]]
    = new below[combinedstream[A]] {
    val `Event_scalaExec.below` = (a : combinedstream[A], b : combinedstream[A])
      => below_combinedstreama[A](a, b)
  }
  implicit def
    `Event_scalaExec.below_sbelem`[A : chan : equal] : below[sbelem[A]] = new
    below[sbelem[A]] {
    val `Event_scalaExec.below` = (a : sbelem[A], b : sbelem[A]) =>
      below_sbelema[A](a, b)
  }
  implicit def
    `Event_scalaExec.below_stream`[A : countable : equal] : below[stream[A]] =
    new below[stream[A]] {
    val `Event_scalaExec.below` = (a : stream[A], b : stream[A]) =>
      below_streama[A](a, b)
  }
  implicit def `Event_scalaExec.below_sb`[A : chan : enuma] : below[sb[A]] = new
    below[sb[A]] {
    val `Event_scalaExec.below` = (a : sb[A], b : sb[A]) =>
      below_sba[A].apply(a).apply(b)
  }
}

trait countable[A] {
}
object countable {
  implicit def
    `Event_scalaExec.countable_msgwithchan`[A : chan : countable] : countable[msgwithchan[A]]
    = new countable[msgwithchan[A]] {
  }
  implicit def
    `Event_scalaExec.countable_tstimed`[A : one_chan : countable] : countable[tstimed[A]]
    = new countable[tstimed[A]] {
  }
  implicit def `Event_scalaExec.countable_channelsa` : countable[channelsa] =
    new countable[channelsa] {
  }
  implicit def `Event_scalaExec.countable_channels` : countable[channels] = new
    countable[channels] {
  }
  implicit def
    `Event_scalaExec.countable_event`[A : countable] : countable[event[A]] = new
    countable[event[A]] {
  }
  implicit def
    `Event_scalaExec.countable_tsyn`[A : countable] : countable[tsyn[A]] = new
    countable[tsyn[A]] {
  }
  implicit def
    `Event_scalaExec.countable_tone`[A : countable] : countable[tone[A]] = new
    countable[tone[A]] {
  }
  implicit def
    `Event_scalaExec.countable_prod`[A : countable,
                                      B : countable] : countable[(A, B)]
    = new countable[(A, B)] {
  }
  implicit def `Event_scalaExec.countable_msg` : countable[msg] = new
    countable[msg] {
  }
  implicit def
    `Event_scalaExec.countable_list`[A : countable] : countable[List[A]] = new
    countable[List[A]] {
  }
  implicit def `Event_scalaExec.countable_m` : countable[M] = new countable[M] {
  }
  implicit def `Event_scalaExec.countable_bool` : countable[Boolean] = new
    countable[Boolean] {
  }
}

trait finite[A] extends countable[A] {
}
object finite {
  implicit def
    `Event_scalaExec.finite_tstimed`[A : one_chan : finite] : finite[tstimed[A]]
    = new finite[tstimed[A]] {
  }
  implicit def `Event_scalaExec.finite_channelsa` : finite[channelsa] = new
    finite[channelsa] {
  }
  implicit def `Event_scalaExec.finite_channels` : finite[channels] = new
    finite[channels] {
  }
}

trait enuma[A] extends finite[A] {
  val `Event_scalaExec.enuma` : List[A]
  val `Event_scalaExec.enum_all` : (A => Boolean) => Boolean
  val `Event_scalaExec.enum_ex` : (A => Boolean) => Boolean
}
def enuma[A](implicit A: enuma[A]) : List[A] = A.`Event_scalaExec.enuma`
def enum_all[A](a : A => Boolean)(implicit A: enuma[A]) : Boolean =
  A.`Event_scalaExec.enum_all`(a)
def enum_ex[A](a : A => Boolean)(implicit A: enuma[A]) : Boolean =
  A.`Event_scalaExec.enum_ex`(a)
object enuma {
  implicit def
    `Event_scalaExec.enum_tstimed`[A : one_chan : enuma] : enuma[tstimed[A]] =
    new enuma[tstimed[A]] {
    val `Event_scalaExec.enuma` = enum_tstimeda[A]
    val `Event_scalaExec.enum_all` = (a : (tstimed[A]) => Boolean) =>
      enum_all_tstimed[A](a)
    val `Event_scalaExec.enum_ex` = (a : (tstimed[A]) => Boolean) =>
      enum_ex_tstimed[A](a)
  }
  implicit def `Event_scalaExec.enum_channelsa` : enuma[channelsa] = new
    enuma[channelsa] {
    val `Event_scalaExec.enuma` = enum_channelsc
    val `Event_scalaExec.enum_all` = (a : channelsa => Boolean) =>
      enum_all_channelsa(a)
    val `Event_scalaExec.enum_ex` = (a : channelsa => Boolean) =>
      enum_ex_channelsa(a)
  }
  implicit def `Event_scalaExec.enum_channels` : enuma[channels] = new
    enuma[channels] {
    val `Event_scalaExec.enuma` = enum_channelsb
    val `Event_scalaExec.enum_all` = (a : channels => Boolean) =>
      enum_all_channels(a)
    val `Event_scalaExec.enum_ex` = (a : channels => Boolean) =>
      enum_ex_channels(a)
  }
}

def All[A : enuma](p : A => Boolean) : Boolean = enum_all[A](p)

def below_fun[A : enuma, B : below] : (A => B) => (A => B) => Boolean =
  ((f : A => B) => (g : A => B) => All[A](((x : A) => below[B](f(x), g(x)))))

abstract sealed class tone[A]
final case class Tonemsg[A](a : A) extends tone[A]

abstract sealed class event[A]
final case class Eventmsg[A](a : A) extends event[A]
final case class Tick[A]() extends event[A]

abstract sealed class tsyn[A]
final case class Tsynmsg[A](a : A) extends tsyn[A]
final case class Eps[A]() extends tsyn[A]

abstract sealed class stream[A]
final case class stream_bottom_nc[A]() extends stream[A]
final case class lscons_u_nc[A](a : A, b : stream[A]) extends stream[A]

abstract sealed class combinedstream[A]
final case class UNTIMEDA[A](a : stream[A]) extends combinedstream[A]
final case class TEVENT[A](a : stream[event[A]]) extends combinedstream[A]
final case class TSLICED[A](a : stream[List[A]]) extends combinedstream[A]
final case class TONEB[A](a : stream[tone[A]]) extends combinedstream[A]
final case class TSYNB[A](a : stream[tsyn[A]]) extends combinedstream[A]

abstract sealed class timetype
final case class Tuntimed() extends timetype
final case class Ttone() extends timetype
final case class Ttfin() extends timetype
final case class Ttlive() extends timetype
final case class Ttsyn() extends timetype

def sconc_nc[A : countable](s1 : stream[A], s2 : stream[A]) : stream[A] =
  (s1, s2) match {
  case (lscons_u_nc(a, s1), s2) => lscons_u_nc[A](a, sconc_nc[A](s1, s2))
  case (stream_bottom_nc(), s2) => s2
  case (s1, stream_bottom_nc()) => s1
}

def sup[A : countable](a : A) : stream[A] =
  lscons_u_nc[A](a, stream_bottom_nc[A]())

def smap_nc[A : countable,
             B : countable](f : A => B, x1 : stream[A]) : stream[B]
  =
  (f, x1) match {
  case (f, stream_bottom_nc()) => stream_bottom_nc[B]()
  case (f, lscons_u_nc(a, as)) =>
    sconc_nc[B](sup[B](f(a)), smap_nc[A, B](f, as))
}

abstract sealed class char
final case class Chara(a : Boolean, b : Boolean, c : Boolean, d : Boolean,
                        e : Boolean, f : Boolean, g : Boolean, h : Boolean)
  extends char

abstract sealed class nat
final case class zero_nat() extends nat
final case class Suc(a : nat) extends nat

abstract sealed class msg
final case class booleventconstr(a : Boolean) extends msg
final case class boolsyncconstr(a : Boolean) extends msg
final case class nateventconstr(a : nat) extends msg
final case class natsyncconstr(a : nat) extends msg
final case class stringeventconstr(a : List[char]) extends msg
final case class stringsyncconstr(a : List[char]) extends msg

abstract sealed class M_timed
final case class Tsyna(a : tsyn[msg]) extends M_timed
final case class Tonea(a : msg) extends M_timed
final case class Tlive(a : event[msg]) extends M_timed
final case class Tfin(a : List[msg]) extends M_timed

abstract sealed class M
final case class Untimed(a : msg) extends M
final case class Timed(a : M_timed) extends M

def inv_untimed(x0 : M) : msg = x0 match {
  case Untimed(x) => x
}

def inv_tlive(x0 : M) : event[msg] = x0 match {
  case Timed(Tlive(x)) => x
}

def inv_tsyn(x0 : M) : tsyn[msg] = x0 match {
  case Timed(Tsyna(x)) => x
}

def inv_tone(x0 : M) : msg = x0 match {
  case Timed(Tonea(x)) => x
}

def inv_tfin(x0 : M) : List[msg] = x0 match {
  case Timed(Tfin(x)) => x
}

def comp[A, B, C](f : A => B, g : C => A) : C => B = ((x : C) => f(g(x)))

def mstream2combined_nc(x0 : timetype, s : stream[M]) : combinedstream[msg] =
  (x0, s) match {
  case (Ttsyn(), s) =>
    TSYNB[msg](smap_nc[M, tsyn[msg]](((a : M) => inv_tsyn(a)), s))
  case (Ttone(), s) =>
    TONEB[msg](smap_nc[M, tone[msg]](comp[msg, tone[msg],
   M](((a : msg) => Tonemsg[msg](a)), ((a : M) => inv_tone(a))),
                                      s))
  case (Ttfin(), s) =>
    TSLICED[msg](smap_nc[M, List[msg]](((a : M) => inv_tfin(a)), s))
  case (Tuntimed(), s) =>
    UNTIMEDA[msg](smap_nc[M, msg](((a : M) => inv_untimed(a)), s))
  case (Ttlive(), s) =>
    TEVENT[msg](smap_nc[M, event[msg]](((a : M) => inv_tlive(a)), s))
}

abstract sealed class msgtype
final case class Tboolevent() extends msgtype
final case class Tboolsync() extends msgtype
final case class Tnatevent() extends msgtype
final case class Tnatsync() extends msgtype
final case class Tstringevent() extends msgtype
final case class Tstringsync() extends msgtype
final case class Tnone() extends msgtype

abstract sealed class channel
final case class CH(a : List[char], b : timetype, c : msgtype) extends channel

abstract sealed class myself[A]
final case class DUMMY[A]() extends myself[A]

abstract sealed class set[A]
final case class seta[A](a : List[A]) extends set[A]
final case class coset[A](a : List[A]) extends set[A]

trait rep[A] {
  val `Event_scalaExec.Rep` : A => channel
  val `Event_scalaExec.Abs` : channel => A
  val `Event_scalaExec.chandom` : (myself[A]) => set[channel]
}
def Rep[A](a : A)(implicit A: rep[A]) : channel = A.`Event_scalaExec.Rep`(a)
def Abs[A](a : channel)(implicit A: rep[A]) : A = A.`Event_scalaExec.Abs`(a)
def chandom[A](a : myself[A])(implicit A: rep[A]) : set[channel] =
  A.`Event_scalaExec.chandom`(a)
object rep {
  implicit def
    `Event_scalaExec.rep_tstimed`[A : one_chan : enuma] : rep[tstimed[A]] = new
    rep[tstimed[A]] {
    val `Event_scalaExec.Rep` = (a : tstimed[A]) => Rep_tstimeda[A](a)
    val `Event_scalaExec.Abs` = (a : channel) => Abs_tstimed[A](a)
    val `Event_scalaExec.chandom` = (a : myself[tstimed[A]]) =>
      chandom_tstimed[A](a)
  }
  implicit def `Event_scalaExec.rep_channelsa` : rep[channelsa] = new
    rep[channelsa] {
    val `Event_scalaExec.Rep` = (a : channelsa) => Rep_channelsc(a)
    val `Event_scalaExec.Abs` = (a : channel) => Abs_channelsa(a)
    val `Event_scalaExec.chandom` = (a : myself[channelsa]) =>
      chandom_channelsa(a)
  }
  implicit def `Event_scalaExec.rep_channels` : rep[channels] = new
    rep[channels] {
    val `Event_scalaExec.Rep` = (a : channels) => Rep_channelsb(a)
    val `Event_scalaExec.Abs` = (a : channel) => Abs_channels(a)
    val `Event_scalaExec.chandom` = (a : myself[channels]) =>
      chandom_channels(a)
  }
}

def ctime(x0 : channel) : timetype = x0 match {
  case CH(uu, tt, uv) => tt
}

trait chan[A] extends rep[A] {
}
object chan {
  implicit def
    `Event_scalaExec.chan_tstimed`[A : one_chan : enuma] : chan[tstimed[A]] =
    new chan[tstimed[A]] {
    val `Event_scalaExec.Rep` = (a : tstimed[A]) => Rep_tstimeda[A](a)
    val `Event_scalaExec.Abs` = (a : channel) => Abs_tstimed[A](a)
    val `Event_scalaExec.chandom` = (a : myself[tstimed[A]]) =>
      chandom_tstimed[A](a)
  }
  implicit def `Event_scalaExec.chan_channelsa` : chan[channelsa] = new
    chan[channelsa] {
    val `Event_scalaExec.Rep` = (a : channelsa) => Rep_channelsc(a)
    val `Event_scalaExec.Abs` = (a : channel) => Abs_channelsa(a)
    val `Event_scalaExec.chandom` = (a : myself[channelsa]) =>
      chandom_channelsa(a)
  }
  implicit def `Event_scalaExec.chan_channels` : chan[channels] = new
    chan[channels] {
    val `Event_scalaExec.Rep` = (a : channels) => Rep_channelsb(a)
    val `Event_scalaExec.Abs` = (a : channel) => Abs_channels(a)
    val `Event_scalaExec.chandom` = (a : myself[channels]) =>
      chandom_channels(a)
  }
}

def sblegacy2new[A : chan](f : A => stream[M], c : A) : combinedstream[msg] =
  mstream2combined_nc(ctime(Rep[A](c)), f(c))

abstract sealed class sb[A]
final case class Abs_lsb[A](a : A => stream[M]) extends sb[A]

def Rep_lsb[A : chan](x0 : sb[A]) : A => stream[M] = x0 match {
  case Abs_lsb(x) => x
}

def Rep_sb[A : chan](sb : sb[A]) : A => combinedstream[msg] =
  ((a : A) => sblegacy2new[A](Rep_lsb[A](sb), a))

trait equal[A] {
  val `Event_scalaExec.equal` : (A, A) => Boolean
}
def equal[A](a : A, b : A)(implicit A: equal[A]) : Boolean =
  A.`Event_scalaExec.equal`(a, b)
object equal {
  implicit def
    `Event_scalaExec.equal_msgwithchan`[A : chan] : equal[msgwithchan[A]] = new
    equal[msgwithchan[A]] {
    val `Event_scalaExec.equal` = (a : msgwithchan[A], b : msgwithchan[A]) =>
      equal_msgwithchana[A](a, b)
  }
  implicit def
    `Event_scalaExec.equal_tstimed`[A : one_chan : equal] : equal[tstimed[A]] =
    new equal[tstimed[A]] {
    val `Event_scalaExec.equal` = (a : tstimed[A], b : tstimed[A]) =>
      equal_tstimeda[A](a, b)
  }
  implicit def `Event_scalaExec.equal_channelsa` : equal[channelsa] = new
    equal[channelsa] {
    val `Event_scalaExec.equal` = (a : channelsa, b : channelsa) =>
      equal_channelsc(a, b)
  }
  implicit def `Event_scalaExec.equal_channels` : equal[channels] = new
    equal[channels] {
    val `Event_scalaExec.equal` = (a : channels, b : channels) =>
      equal_channelsb(a, b)
  }
  implicit def `Event_scalaExec.equal_event`[A : equal] : equal[event[A]] = new
    equal[event[A]] {
    val `Event_scalaExec.equal` = (a : event[A], b : event[A]) =>
      equal_eventa[A](a, b)
  }
  implicit def `Event_scalaExec.equal_tsyn`[A : equal] : equal[tsyn[A]] = new
    equal[tsyn[A]] {
    val `Event_scalaExec.equal` = (a : tsyn[A], b : tsyn[A]) =>
      equal_tsyna[A](a, b)
  }
  implicit def `Event_scalaExec.equal_tone`[A : equal] : equal[tone[A]] = new
    equal[tone[A]] {
    val `Event_scalaExec.equal` = (a : tone[A], b : tone[A]) =>
      equal_tonea[A](a, b)
  }
  implicit def
    `Event_scalaExec.equal_prod`[A : equal, B : equal] : equal[(A, B)] = new
    equal[(A, B)] {
    val `Event_scalaExec.equal` = (a : (A, B), b : (A, B)) =>
      equal_proda[A, B](a, b)
  }
  implicit def `Event_scalaExec.equal_channel` : equal[channel] = new
    equal[channel] {
    val `Event_scalaExec.equal` = (a : channel, b : channel) =>
      equal_channela(a, b)
  }
  implicit def
    `Event_scalaExec.equal_sbelem`[A : chan : equal] : equal[sbelem[A]] = new
    equal[sbelem[A]] {
    val `Event_scalaExec.equal` = (a : sbelem[A], b : sbelem[A]) =>
      equal_sbelema[A](a, b)
  }
  implicit def `Event_scalaExec.equal_msg` : equal[msg] = new equal[msg] {
    val `Event_scalaExec.equal` = (a : msg, b : msg) => equal_msga(a, b)
  }
  implicit def `Event_scalaExec.equal_char` : equal[char] = new equal[char] {
    val `Event_scalaExec.equal` = (a : char, b : char) => equal_chara(a, b)
  }
  implicit def `Event_scalaExec.equal_list`[A : equal] : equal[List[A]] = new
    equal[List[A]] {
    val `Event_scalaExec.equal` = (a : List[A], b : List[A]) =>
      equal_lista[A](a, b)
  }
  implicit def `Event_scalaExec.equal_m` : equal[M] = new equal[M] {
    val `Event_scalaExec.equal` = (a : M, b : M) => equal_ma(a, b)
  }
  implicit def `Event_scalaExec.equal_bool` : equal[Boolean] = new
    equal[Boolean] {
    val `Event_scalaExec.equal` = (a : Boolean, b : Boolean) =>
      equal_boola(a, b)
  }
}

def eq[A : equal](a : A, b : A) : Boolean = equal[A](a, b)

def below_streama[A : countable : equal](x0 : stream[A],
  as : stream[A]) : Boolean
  =
  (x0, as) match {
  case (lscons_u_nc(a, as), lscons_u_nc(b, bs)) =>
    (! (eq[A](a, b)) match { case true => false
      case false => below_streama[A](as, bs) })
  case (stream_bottom_nc(), as) => true
}

def equal_eventa[A : equal](x0 : event[A], x1 : event[A]) : Boolean = (x0, x1)
  match {
  case (Eventmsg(x1), Tick()) => false
  case (Tick(), Eventmsg(x1)) => false
  case (Eventmsg(x1), Eventmsg(y1)) => eq[A](x1, y1)
  case (Tick(), Tick()) => true
}

def equal_tsyna[A : equal](x0 : tsyn[A], x1 : tsyn[A]) : Boolean = (x0, x1)
  match {
  case (Tsynmsg(x1), Eps()) => false
  case (Eps(), Tsynmsg(x1)) => false
  case (Tsynmsg(x1), Tsynmsg(y1)) => eq[A](x1, y1)
  case (Eps(), Eps()) => true
}

def equal_tonea[A : equal](x0 : tone[A], x1 : tone[A]) : Boolean = (x0, x1)
  match {
  case (Tonemsg(x), Tonemsg(ya)) => eq[A](x, ya)
}

def equal_lista[A : equal](x0 : List[A], x1 : List[A]) : Boolean = (x0, x1)
  match {
  case (Nil, x21 :: x22) => false
  case (x21 :: x22, Nil) => false
  case (x21 :: x22, y21 :: y22) => eq[A](x21, y21) && equal_lista[A](x22, y22)
  case (Nil, Nil) => true
}

def below_combinedstreama[A : countable : equal](x0 : combinedstream[A],
          x1 : combinedstream[A]) : Boolean
  =
  (x0, x1) match {
  case (UNTIMEDA(a), UNTIMEDA(b)) => below_streama[A](a, b)
  case (TEVENT(a), TEVENT(b)) => below_streama[event[A]](a, b)
  case (TSLICED(a), TSLICED(b)) => below_streama[List[A]](a, b)
  case (TONEB(a), TONEB(b)) => below_streama[tone[A]](a, b)
  case (TSYNB(a), TSYNB(b)) => below_streama[tsyn[A]](a, b)
  case (TEVENT(v), UNTIMEDA(va)) => false
  case (TEVENT(v), TSLICED(va)) => false
  case (TEVENT(v), TONEB(va)) => false
  case (TEVENT(v), TSYNB(va)) => false
  case (TSLICED(v), UNTIMEDA(va)) => false
  case (TSLICED(v), TEVENT(va)) => false
  case (TSLICED(v), TONEB(va)) => false
  case (TSLICED(v), TSYNB(va)) => false
  case (TONEB(v), UNTIMEDA(va)) => false
  case (TONEB(v), TEVENT(va)) => false
  case (TONEB(v), TSLICED(va)) => false
  case (TONEB(v), TSYNB(va)) => false
  case (TSYNB(v), UNTIMEDA(va)) => false
  case (TSYNB(v), TEVENT(va)) => false
  case (TSYNB(v), TSLICED(va)) => false
  case (TSYNB(v), TONEB(va)) => false
  case (UNTIMEDA(va), TEVENT(v)) => false
  case (UNTIMEDA(va), TSLICED(v)) => false
  case (UNTIMEDA(va), TONEB(v)) => false
  case (UNTIMEDA(va), TSYNB(v)) => false
}

def equal_boola(p : Boolean, pa : Boolean) : Boolean = (p, pa) match {
  case (p, true) => p
  case (p, false) => ! p
  case (true, p) => p
  case (false, p) => ! p
}

def equal_nat(x0 : nat, x1 : nat) : Boolean = (x0, x1) match {
  case (zero_nat(), Suc(x2)) => false
  case (Suc(x2), zero_nat()) => false
  case (Suc(x2), Suc(y2)) => equal_nat(x2, y2)
  case (zero_nat(), zero_nat()) => true
}

def equal_chara(x0 : char, x1 : char) : Boolean = (x0, x1) match {
  case (Chara(x1, x2, x3, x4, x5, x6, x7, x8),
         Chara(y1, y2, y3, y4, y5, y6, y7, y8))
    => equal_boola(x1, y1) &&
         (equal_boola(x2, y2) &&
           (equal_boola(x3, y3) &&
             (equal_boola(x4, y4) &&
               (equal_boola(x5, y5) &&
                 (equal_boola(x6, y6) &&
                   (equal_boola(x7, y7) && equal_boola(x8, y8)))))))
}

def equal_msga(x0 : msg, x1 : msg) : Boolean = (x0, x1) match {
  case (stringeventconstr(x5), stringsyncconstr(x6)) => false
  case (stringsyncconstr(x6), stringeventconstr(x5)) => false
  case (natsyncconstr(x4), stringsyncconstr(x6)) => false
  case (stringsyncconstr(x6), natsyncconstr(x4)) => false
  case (natsyncconstr(x4), stringeventconstr(x5)) => false
  case (stringeventconstr(x5), natsyncconstr(x4)) => false
  case (nateventconstr(x3), stringsyncconstr(x6)) => false
  case (stringsyncconstr(x6), nateventconstr(x3)) => false
  case (nateventconstr(x3), stringeventconstr(x5)) => false
  case (stringeventconstr(x5), nateventconstr(x3)) => false
  case (nateventconstr(x3), natsyncconstr(x4)) => false
  case (natsyncconstr(x4), nateventconstr(x3)) => false
  case (boolsyncconstr(x2), stringsyncconstr(x6)) => false
  case (stringsyncconstr(x6), boolsyncconstr(x2)) => false
  case (boolsyncconstr(x2), stringeventconstr(x5)) => false
  case (stringeventconstr(x5), boolsyncconstr(x2)) => false
  case (boolsyncconstr(x2), natsyncconstr(x4)) => false
  case (natsyncconstr(x4), boolsyncconstr(x2)) => false
  case (boolsyncconstr(x2), nateventconstr(x3)) => false
  case (nateventconstr(x3), boolsyncconstr(x2)) => false
  case (booleventconstr(x1), stringsyncconstr(x6)) => false
  case (stringsyncconstr(x6), booleventconstr(x1)) => false
  case (booleventconstr(x1), stringeventconstr(x5)) => false
  case (stringeventconstr(x5), booleventconstr(x1)) => false
  case (booleventconstr(x1), natsyncconstr(x4)) => false
  case (natsyncconstr(x4), booleventconstr(x1)) => false
  case (booleventconstr(x1), nateventconstr(x3)) => false
  case (nateventconstr(x3), booleventconstr(x1)) => false
  case (booleventconstr(x1), boolsyncconstr(x2)) => false
  case (boolsyncconstr(x2), booleventconstr(x1)) => false
  case (stringsyncconstr(x6), stringsyncconstr(y6)) => equal_lista[char](x6, y6)
  case (stringeventconstr(x5), stringeventconstr(y5)) =>
    equal_lista[char](x5, y5)
  case (natsyncconstr(x4), natsyncconstr(y4)) => equal_nat(x4, y4)
  case (nateventconstr(x3), nateventconstr(y3)) => equal_nat(x3, y3)
  case (boolsyncconstr(x2), boolsyncconstr(y2)) => equal_boola(x2, y2)
  case (booleventconstr(x1), booleventconstr(y1)) => equal_boola(x1, y1)
}

def below_sba[A : chan : enuma] : (sb[A]) => (sb[A]) => Boolean =
  ((x : sb[A]) => (y : sb[A]) =>
    below_fun[A, combinedstream[msg]].apply(Rep_sb[A](x)).apply(Rep_sb[A](y)))

trait po[A] extends below[A] {
}
object po {
  implicit def `Event_scalaExec.po_sbelem`[A : chan : equal] : po[sbelem[A]] =
    new po[sbelem[A]] {
    val `Event_scalaExec.below` = (a : sbelem[A], b : sbelem[A]) =>
      below_sbelema[A](a, b)
  }
  implicit def
    `Event_scalaExec.po_stream`[A : countable : equal] : po[stream[A]] = new
    po[stream[A]] {
    val `Event_scalaExec.below` = (a : stream[A], b : stream[A]) =>
      below_streama[A](a, b)
  }
  implicit def `Event_scalaExec.po_sb`[A : chan : enuma] : po[sb[A]] = new
    po[sb[A]] {
    val `Event_scalaExec.below` = (a : sb[A], b : sb[A]) =>
      below_sba[A].apply(a).apply(b)
  }
}

trait cpo[A] extends po[A] {
}
object cpo {
  implicit def `Event_scalaExec.cpo_sbelem`[A : chan : equal] : cpo[sbelem[A]] =
    new cpo[sbelem[A]] {
    val `Event_scalaExec.below` = (a : sbelem[A], b : sbelem[A]) =>
      below_sbelema[A](a, b)
  }
  implicit def
    `Event_scalaExec.cpo_stream`[A : countable : equal] : cpo[stream[A]] = new
    cpo[stream[A]] {
    val `Event_scalaExec.below` = (a : stream[A], b : stream[A]) =>
      below_streama[A](a, b)
  }
  implicit def `Event_scalaExec.cpo_sb`[A : chan : enuma] : cpo[sb[A]] = new
    cpo[sb[A]] {
    val `Event_scalaExec.below` = (a : sb[A], b : sb[A]) =>
      below_sba[A].apply(a).apply(b)
  }
}

trait pcpo[A] extends cpo[A] {
}
object pcpo {
  implicit def
    `Event_scalaExec.pcpo_stream`[A : countable : equal] : pcpo[stream[A]] = new
    pcpo[stream[A]] {
    val `Event_scalaExec.below` = (a : stream[A], b : stream[A]) =>
      below_streama[A](a, b)
  }
  implicit def `Event_scalaExec.pcpo_sb`[A : chan : enuma] : pcpo[sb[A]] = new
    pcpo[sb[A]] {
    val `Event_scalaExec.below` = (a : sb[A], b : sb[A]) =>
      below_sba[A].apply(a).apply(b)
  }
}

def sbconc_nc[A : chan](sb1 : sb[A], sb2 : sb[A]) : sb[A] =
  Abs_lsb[A](((c : A) =>
               sconc_nc[M]((Rep_lsb[A](sb1)).apply(c),
                            (Rep_lsb[A](sb2)).apply(c))))

abstract sealed class cfun[B, A]
final case class Abs_cfun[B, A](a : B => A) extends cfun[B, A]

def conc_sba[A : chan : enuma](sb : sb[A]) : cfun[sb[A], sb[A]] =
  Abs_cfun[sb[A], sb[A]](((a : sb[A]) => sbconc_nc[A](sb, a)))

trait conc[A] extends pcpo[A] {
  val `Event_scalaExec.conc` : A => cfun[A, A]
}
def conc[A](a : A)(implicit A: conc[A]) : cfun[A, A] =
  A.`Event_scalaExec.conc`(a)
object conc {
  implicit def
    `Event_scalaExec.conc_stream`[A : countable : equal] : conc[stream[A]] = new
    conc[stream[A]] {
    val `Event_scalaExec.conc` = (a : stream[A]) => conc_streama[A](a)
    val `Event_scalaExec.below` = (a : stream[A], b : stream[A]) =>
      below_streama[A](a, b)
  }
  implicit def `Event_scalaExec.conc_sb`[A : chan : enuma] : conc[sb[A]] = new
    conc[sb[A]] {
    val `Event_scalaExec.conc` = (a : sb[A]) => conc_sba[A](a)
    val `Event_scalaExec.below` = (a : sb[A], b : sb[A]) =>
      below_sba[A].apply(a).apply(b)
  }
}

def bot_nc_streama[A : countable] : stream[A] = stream_bottom_nc[A]()

def bot_nc_sba[A : chan] : sb[A] = Abs_lsb[A](((_ : A) => bot_nc_streama[M]))

trait bot_nc[A] extends pcpo[A] {
  val `Event_scalaExec.bot_nc` : A
}
def bot_nc[A](implicit A: bot_nc[A]) : A = A.`Event_scalaExec.bot_nc`
object bot_nc {
  implicit def
    `Event_scalaExec.bot_nc_stream`[A : countable : equal] : bot_nc[stream[A]] =
    new bot_nc[stream[A]] {
    val `Event_scalaExec.bot_nc` = bot_nc_streama[A]
    val `Event_scalaExec.below` = (a : stream[A], b : stream[A]) =>
      below_streama[A](a, b)
  }
  implicit def `Event_scalaExec.bot_nc_sb`[A : chan : enuma] : bot_nc[sb[A]] =
    new bot_nc[sb[A]] {
    val `Event_scalaExec.bot_nc` = bot_nc_sba[A]
    val `Event_scalaExec.below` = (a : sb[A], b : sb[A]) =>
      below_sba[A].apply(a).apply(b)
  }
}

def equal_m_timed(x0 : M_timed, x1 : M_timed) : Boolean = (x0, x1) match {
  case (Tlive(x3), Tfin(x4)) => false
  case (Tfin(x4), Tlive(x3)) => false
  case (Tonea(x2), Tfin(x4)) => false
  case (Tfin(x4), Tonea(x2)) => false
  case (Tonea(x2), Tlive(x3)) => false
  case (Tlive(x3), Tonea(x2)) => false
  case (Tsyna(x1), Tfin(x4)) => false
  case (Tfin(x4), Tsyna(x1)) => false
  case (Tsyna(x1), Tlive(x3)) => false
  case (Tlive(x3), Tsyna(x1)) => false
  case (Tsyna(x1), Tonea(x2)) => false
  case (Tonea(x2), Tsyna(x1)) => false
  case (Tfin(x4), Tfin(y4)) => equal_lista[msg](x4, y4)
  case (Tlive(x3), Tlive(y3)) => equal_eventa[msg](x3, y3)
  case (Tonea(x2), Tonea(y2)) => equal_msga(x2, y2)
  case (Tsyna(x1), Tsyna(y1)) => equal_tsyna[msg](x1, y1)
}

def equal_ma(x0 : M, x1 : M) : Boolean = (x0, x1) match {
  case (Untimed(x1), Timed(x2)) => false
  case (Timed(x2), Untimed(x1)) => false
  case (Timed(x2), Timed(y2)) => equal_m_timed(x2, y2)
  case (Untimed(x1), Untimed(y1)) => equal_msga(x1, y1)
}

def conc_streama[A : countable : equal](s1 : stream[A]) : cfun[stream[A],
                        stream[A]]
  =
  Abs_cfun[stream[A], stream[A]](((a : stream[A]) => sconc_nc[A](s1, a)))

abstract sealed class sbelem[A]
final case class Abs_sbelem[A](a : Option[A => M]) extends sbelem[A]

def equal_sbelema[A : chan : equal](a : sbelem[A], b : sbelem[A]) : Boolean =
  equal_sbelema[A](a, b)

def below_sbelema[A : chan : equal](sbe1 : sbelem[A],
                                     sbe2 : sbelem[A]) : Boolean
  =
  eq[sbelem[A]](sbe1, sbe2)

def equal_timetype(x0 : timetype, x1 : timetype) : Boolean = (x0, x1) match {
  case (Ttlive(), Ttsyn()) => false
  case (Ttsyn(), Ttlive()) => false
  case (Ttfin(), Ttsyn()) => false
  case (Ttsyn(), Ttfin()) => false
  case (Ttfin(), Ttlive()) => false
  case (Ttlive(), Ttfin()) => false
  case (Ttone(), Ttsyn()) => false
  case (Ttsyn(), Ttone()) => false
  case (Ttone(), Ttlive()) => false
  case (Ttlive(), Ttone()) => false
  case (Ttone(), Ttfin()) => false
  case (Ttfin(), Ttone()) => false
  case (Tuntimed(), Ttsyn()) => false
  case (Ttsyn(), Tuntimed()) => false
  case (Tuntimed(), Ttlive()) => false
  case (Ttlive(), Tuntimed()) => false
  case (Tuntimed(), Ttfin()) => false
  case (Ttfin(), Tuntimed()) => false
  case (Tuntimed(), Ttone()) => false
  case (Ttone(), Tuntimed()) => false
  case (Ttsyn(), Ttsyn()) => true
  case (Ttlive(), Ttlive()) => true
  case (Ttfin(), Ttfin()) => true
  case (Ttone(), Ttone()) => true
  case (Tuntimed(), Tuntimed()) => true
}

def equal_msgtype(x0 : msgtype, x1 : msgtype) : Boolean = (x0, x1) match {
  case (Tstringsync(), Tnone()) => false
  case (Tnone(), Tstringsync()) => false
  case (Tstringevent(), Tnone()) => false
  case (Tnone(), Tstringevent()) => false
  case (Tstringevent(), Tstringsync()) => false
  case (Tstringsync(), Tstringevent()) => false
  case (Tnatsync(), Tnone()) => false
  case (Tnone(), Tnatsync()) => false
  case (Tnatsync(), Tstringsync()) => false
  case (Tstringsync(), Tnatsync()) => false
  case (Tnatsync(), Tstringevent()) => false
  case (Tstringevent(), Tnatsync()) => false
  case (Tnatevent(), Tnone()) => false
  case (Tnone(), Tnatevent()) => false
  case (Tnatevent(), Tstringsync()) => false
  case (Tstringsync(), Tnatevent()) => false
  case (Tnatevent(), Tstringevent()) => false
  case (Tstringevent(), Tnatevent()) => false
  case (Tnatevent(), Tnatsync()) => false
  case (Tnatsync(), Tnatevent()) => false
  case (Tboolsync(), Tnone()) => false
  case (Tnone(), Tboolsync()) => false
  case (Tboolsync(), Tstringsync()) => false
  case (Tstringsync(), Tboolsync()) => false
  case (Tboolsync(), Tstringevent()) => false
  case (Tstringevent(), Tboolsync()) => false
  case (Tboolsync(), Tnatsync()) => false
  case (Tnatsync(), Tboolsync()) => false
  case (Tboolsync(), Tnatevent()) => false
  case (Tnatevent(), Tboolsync()) => false
  case (Tboolevent(), Tnone()) => false
  case (Tnone(), Tboolevent()) => false
  case (Tboolevent(), Tstringsync()) => false
  case (Tstringsync(), Tboolevent()) => false
  case (Tboolevent(), Tstringevent()) => false
  case (Tstringevent(), Tboolevent()) => false
  case (Tboolevent(), Tnatsync()) => false
  case (Tnatsync(), Tboolevent()) => false
  case (Tboolevent(), Tnatevent()) => false
  case (Tnatevent(), Tboolevent()) => false
  case (Tboolevent(), Tboolsync()) => false
  case (Tboolsync(), Tboolevent()) => false
  case (Tnone(), Tnone()) => true
  case (Tstringsync(), Tstringsync()) => true
  case (Tstringevent(), Tstringevent()) => true
  case (Tnatsync(), Tnatsync()) => true
  case (Tnatevent(), Tnatevent()) => true
  case (Tboolsync(), Tboolsync()) => true
  case (Tboolevent(), Tboolevent()) => true
}

def equal_channela(x0 : channel, x1 : channel) : Boolean = (x0, x1) match {
  case (CH(x1, x2, x3), CH(y1, y2, y3)) =>
    equal_lista[char](x1, y1) &&
      (equal_timetype(x2, y2) && equal_msgtype(x3, y3))
}

def equal_proda[A : equal, B : equal](x0 : (A, B), x1 : (A, B)) : Boolean =
  (x0, x1) match {
  case ((x1, x2), (y1, y2)) => eq[A](x1, y1) && eq[B](x2, y2)
}

abstract sealed class channels
final case class beinchannel_rep() extends channels

def enum_channelsb : List[channels] = List(beinchannel_rep())

def list_all[A](p : A => Boolean, x1 : List[A]) : Boolean = (p, x1) match {
  case (p, Nil) => true
  case (p, x :: xs) => p(x) && list_all[A](p, xs)
}

def enum_all_channels(p : channels => Boolean) : Boolean =
  list_all[channels](p, enum_channelsb)

def list_ex[A](p : A => Boolean, x1 : List[A]) : Boolean = (p, x1) match {
  case (p, Nil) => false
  case (p, x :: xs) => p(x) || list_ex[A](p, xs)
}

def enum_ex_channels(p : channels => Boolean) : Boolean =
  list_ex[channels](p, enum_channelsb)

def equal_channelsb(x0 : channels, x1 : channels) : Boolean = (x0, x1) match {
  case (beinchannel_rep(), beinchannel_rep()) => true
}

def bot_set[A] : set[A] = seta[A](Nil)

def removeall[A : equal](x : A, xa1 : List[A]) : List[A] = (x, xa1) match {
  case (x, Nil) => Nil
  case (x, y :: xs) =>
    (eq[A](x, y) match { case true => removeall[A](x, xs)
      case false => y :: removeall[A](x, xs) })
}

def membera[A : equal](x0 : List[A], y : A) : Boolean = (x0, y) match {
  case (Nil, y) => false
  case (x :: xs, y) => eq[A](x, y) || membera[A](xs, y)
}

def inserta[A : equal](x : A, xs : List[A]) : List[A] =
  (membera[A](xs, x) match { case true => xs case false => x :: xs })

def insert[A : equal](x : A, xa1 : set[A]) : set[A] = (x, xa1) match {
  case (x, coset(xs)) => coset[A](removeall[A](x, xs))
  case (x, seta(xs)) => seta[A](inserta[A](x, xs))
}

def chandom_channels(a : myself[channels]) : set[channel] =
  insert[channel](CH(List(Chara(false, true, false, false, false, true, true,
                                 false),
                           Chara(true, false, true, false, false, true, true,
                                  false),
                           Chara(true, false, false, true, false, false, true,
                                  false),
                           Chara(false, true, true, true, false, true, true,
                                  false),
                           Chara(true, true, false, false, false, false, true,
                                  false),
                           Chara(false, false, false, true, false, true, true,
                                  false),
                           Chara(true, false, false, false, false, true, true,
                                  false),
                           Chara(false, true, true, true, false, true, true,
                                  false),
                           Chara(false, true, true, true, false, true, true,
                                  false),
                           Chara(true, false, true, false, false, true, true,
                                  false),
                           Chara(false, false, true, true, false, true, true,
                                  false),
                           Chara(true, true, true, true, true, false, true,
                                  false),
                           Chara(false, true, false, false, true, true, true,
                                  false),
                           Chara(true, false, true, false, false, true, true,
                                  false),
                           Chara(false, false, false, false, true, true, true,
                                  false)),
                      Ttlive(), Tboolevent()),
                   bot_set[channel])

def Rep_channelsb(x0 : channels) : channel = x0 match {
  case beinchannel_rep() =>
    CH(List(Chara(false, true, false, false, false, true, true, false),
             Chara(true, false, true, false, false, true, true, false),
             Chara(true, false, false, true, false, false, true, false),
             Chara(false, true, true, true, false, true, true, false),
             Chara(true, true, false, false, false, false, true, false),
             Chara(false, false, false, true, false, true, true, false),
             Chara(true, false, false, false, false, true, true, false),
             Chara(false, true, true, true, false, true, true, false),
             Chara(false, true, true, true, false, true, true, false),
             Chara(true, false, true, false, false, true, true, false),
             Chara(false, false, true, true, false, true, true, false),
             Chara(true, true, true, true, true, false, true, false),
             Chara(false, true, false, false, true, true, true, false),
             Chara(true, false, true, false, false, true, true, false),
             Chara(false, false, false, false, true, true, true, false)),
        Ttlive(), Tboolevent())
}

def Abs_channels(x0 : channel) : channels = x0 match {
  case CH(List(Chara(false, true, false, false, false, true, true, false),
                Chara(true, false, true, false, false, true, true, false),
                Chara(true, false, false, true, false, false, true, false),
                Chara(false, true, true, true, false, true, true, false),
                Chara(true, true, false, false, false, false, true, false),
                Chara(false, false, false, true, false, true, true, false),
                Chara(true, false, false, false, false, true, true, false),
                Chara(false, true, true, true, false, true, true, false),
                Chara(false, true, true, true, false, true, true, false),
                Chara(true, false, true, false, false, true, true, false),
                Chara(false, false, true, true, false, true, true, false),
                Chara(true, true, true, true, true, false, true, false),
                Chara(false, true, false, false, true, true, true, false),
                Chara(true, false, true, false, false, true, true, false),
                Chara(false, false, false, false, true, true, true, false)),
           Ttlive(), Tboolevent())
    => beinchannel_rep()
}

trait one_chan[A] extends chan[A] {
}
object one_chan {
  implicit def `Event_scalaExec.one_chan_channelsa` : one_chan[channelsa] = new
    one_chan[channelsa] {
    val `Event_scalaExec.Rep` = (a : channelsa) => Rep_channelsc(a)
    val `Event_scalaExec.Abs` = (a : channel) => Abs_channelsa(a)
    val `Event_scalaExec.chandom` = (a : myself[channelsa]) =>
      chandom_channelsa(a)
  }
  implicit def `Event_scalaExec.one_chan_channels` : one_chan[channels] = new
    one_chan[channels] {
    val `Event_scalaExec.Rep` = (a : channels) => Rep_channelsb(a)
    val `Event_scalaExec.Abs` = (a : channel) => Abs_channels(a)
    val `Event_scalaExec.chandom` = (a : myself[channels]) =>
      chandom_channels(a)
  }
}

trait mult_msg_chan[A] extends chan[A] {
}
object mult_msg_chan {
  implicit def
    `Event_scalaExec.mult_msg_chan_channelsa` : mult_msg_chan[channelsa] = new
    mult_msg_chan[channelsa] {
    val `Event_scalaExec.Rep` = (a : channelsa) => Rep_channelsc(a)
    val `Event_scalaExec.Abs` = (a : channel) => Abs_channelsa(a)
    val `Event_scalaExec.chandom` = (a : myself[channelsa]) =>
      chandom_channelsa(a)
  }
  implicit def
    `Event_scalaExec.mult_msg_chan_channels` : mult_msg_chan[channels] = new
    mult_msg_chan[channels] {
    val `Event_scalaExec.Rep` = (a : channels) => Rep_channelsb(a)
    val `Event_scalaExec.Abs` = (a : channel) => Abs_channels(a)
    val `Event_scalaExec.chandom` = (a : myself[channels]) =>
      chandom_channels(a)
  }
}

trait tchan[A] extends chan[A] {
}
object tchan {
  implicit def
    `Event_scalaExec.tchan_tstimed`[A : one_chan : enuma] : tchan[tstimed[A]] =
    new tchan[tstimed[A]] {
    val `Event_scalaExec.Rep` = (a : tstimed[A]) => Rep_tstimeda[A](a)
    val `Event_scalaExec.Abs` = (a : channel) => Abs_tstimed[A](a)
    val `Event_scalaExec.chandom` = (a : myself[tstimed[A]]) =>
      chandom_tstimed[A](a)
  }
  implicit def `Event_scalaExec.tchan_channelsa` : tchan[channelsa] = new
    tchan[channelsa] {
    val `Event_scalaExec.Rep` = (a : channelsa) => Rep_channelsc(a)
    val `Event_scalaExec.Abs` = (a : channel) => Abs_channelsa(a)
    val `Event_scalaExec.chandom` = (a : myself[channelsa]) =>
      chandom_channelsa(a)
  }
  implicit def `Event_scalaExec.tchan_channels` : tchan[channels] = new
    tchan[channels] {
    val `Event_scalaExec.Rep` = (a : channels) => Rep_channelsb(a)
    val `Event_scalaExec.Abs` = (a : channel) => Abs_channels(a)
    val `Event_scalaExec.chandom` = (a : myself[channels]) =>
      chandom_channels(a)
  }
}

trait echan[A] extends mult_msg_chan[A] with tchan[A] with one_chan[A] {
}
object echan {
  implicit def `Event_scalaExec.echan_channelsa` : echan[channelsa] = new
    echan[channelsa] {
    val `Event_scalaExec.Rep` = (a : channelsa) => Rep_channelsc(a)
    val `Event_scalaExec.Abs` = (a : channel) => Abs_channelsa(a)
    val `Event_scalaExec.chandom` = (a : myself[channelsa]) =>
      chandom_channelsa(a)
  }
  implicit def `Event_scalaExec.echan_channels` : echan[channels] = new
    echan[channels] {
    val `Event_scalaExec.Rep` = (a : channels) => Rep_channelsb(a)
    val `Event_scalaExec.Abs` = (a : channel) => Abs_channels(a)
    val `Event_scalaExec.chandom` = (a : myself[channels]) =>
      chandom_channels(a)
  }
}

abstract sealed class num
final case class Onea() extends num
final case class Bit0(a : num) extends num
final case class Bit1(a : num) extends num

def one_integera : BigInt = BigInt(1)

trait one[A] {
  val `Event_scalaExec.one` : A
}
def one[A](implicit A: one[A]) : A = A.`Event_scalaExec.one`
object one {
  implicit def `Event_scalaExec.one_integer` : one[BigInt] = new one[BigInt] {
    val `Event_scalaExec.one` = one_integera
  }
}

trait plus[A] {
  val `Event_scalaExec.plus` : (A, A) => A
}
def plus[A](a : A, b : A)(implicit A: plus[A]) : A =
  A.`Event_scalaExec.plus`(a, b)
object plus {
  implicit def `Event_scalaExec.plus_natural` : plus[natural] = new
    plus[natural] {
    val `Event_scalaExec.plus` = (a : natural, b : natural) =>
      plus_naturala(a, b)
  }
  implicit def `Event_scalaExec.plus_integer` : plus[BigInt] = new plus[BigInt]
    {
    val `Event_scalaExec.plus` = (a : BigInt, b : BigInt) => a + b
  }
}

trait zero[A] {
  val `Event_scalaExec.zero` : A
}
def zero[A](implicit A: zero[A]) : A = A.`Event_scalaExec.zero`
object zero {
  implicit def `Event_scalaExec.zero_natural` : zero[natural] = new
    zero[natural] {
    val `Event_scalaExec.zero` = zero_naturala
  }
  implicit def `Event_scalaExec.zero_integer` : zero[BigInt] = new zero[BigInt]
    {
    val `Event_scalaExec.zero` = BigInt(0)
  }
}

trait semigroup_add[A] extends plus[A] {
}
object semigroup_add {
  implicit def `Event_scalaExec.semigroup_add_natural` : semigroup_add[natural]
    = new semigroup_add[natural] {
    val `Event_scalaExec.plus` = (a : natural, b : natural) =>
      plus_naturala(a, b)
  }
  implicit def `Event_scalaExec.semigroup_add_integer` : semigroup_add[BigInt] =
    new semigroup_add[BigInt] {
    val `Event_scalaExec.plus` = (a : BigInt, b : BigInt) => a + b
  }
}

trait numeral[A] extends one[A] with semigroup_add[A] {
}
object numeral {
  implicit def `Event_scalaExec.numeral_integer` : numeral[BigInt] = new
    numeral[BigInt] {
    val `Event_scalaExec.plus` = (a : BigInt, b : BigInt) => a + b
    val `Event_scalaExec.one` = one_integera
  }
}

trait times[A] {
  val `Event_scalaExec.times` : (A, A) => A
}
def times[A](a : A, b : A)(implicit A: times[A]) : A =
  A.`Event_scalaExec.times`(a, b)
object times {
  implicit def `Event_scalaExec.times_integer` : times[BigInt] = new
    times[BigInt] {
    val `Event_scalaExec.times` = (a : BigInt, b : BigInt) => a * b
  }
}

trait power[A] extends one[A] with times[A] {
}
object power {
  implicit def `Event_scalaExec.power_integer` : power[BigInt] = new
    power[BigInt] {
    val `Event_scalaExec.times` = (a : BigInt, b : BigInt) => a * b
    val `Event_scalaExec.one` = one_integera
  }
}

trait ord[A] {
  val `Event_scalaExec.less_eq` : (A, A) => Boolean
  val `Event_scalaExec.less` : (A, A) => Boolean
}
def less_eq[A](a : A, b : A)(implicit A: ord[A]) : Boolean =
  A.`Event_scalaExec.less_eq`(a, b)
def less[A](a : A, b : A)(implicit A: ord[A]) : Boolean =
  A.`Event_scalaExec.less`(a, b)
object ord {
  implicit def `Event_scalaExec.ord_integer` : ord[BigInt] = new ord[BigInt] {
    val `Event_scalaExec.less_eq` = (a : BigInt, b : BigInt) => a <= b
    val `Event_scalaExec.less` = (a : BigInt, b : BigInt) => a < b
  }
}

trait ab_semigroup_add[A] extends semigroup_add[A] {
}
object ab_semigroup_add {
  implicit def
    `Event_scalaExec.ab_semigroup_add_integer` : ab_semigroup_add[BigInt] = new
    ab_semigroup_add[BigInt] {
    val `Event_scalaExec.plus` = (a : BigInt, b : BigInt) => a + b
  }
}

trait semigroup_mult[A] extends times[A] {
}
object semigroup_mult {
  implicit def `Event_scalaExec.semigroup_mult_integer` : semigroup_mult[BigInt]
    = new semigroup_mult[BigInt] {
    val `Event_scalaExec.times` = (a : BigInt, b : BigInt) => a * b
  }
}

trait semiring[A] extends ab_semigroup_add[A] with semigroup_mult[A] {
}
object semiring {
  implicit def `Event_scalaExec.semiring_integer` : semiring[BigInt] = new
    semiring[BigInt] {
    val `Event_scalaExec.times` = (a : BigInt, b : BigInt) => a * b
    val `Event_scalaExec.plus` = (a : BigInt, b : BigInt) => a + b
  }
}

trait mult_zero[A] extends times[A] with zero[A] {
}
object mult_zero {
  implicit def `Event_scalaExec.mult_zero_integer` : mult_zero[BigInt] = new
    mult_zero[BigInt] {
    val `Event_scalaExec.zero` = BigInt(0)
    val `Event_scalaExec.times` = (a : BigInt, b : BigInt) => a * b
  }
}

trait monoid_add[A] extends semigroup_add[A] with zero[A] {
}
object monoid_add {
  implicit def `Event_scalaExec.monoid_add_natural` : monoid_add[natural] = new
    monoid_add[natural] {
    val `Event_scalaExec.zero` = zero_naturala
    val `Event_scalaExec.plus` = (a : natural, b : natural) =>
      plus_naturala(a, b)
  }
  implicit def `Event_scalaExec.monoid_add_integer` : monoid_add[BigInt] = new
    monoid_add[BigInt] {
    val `Event_scalaExec.zero` = BigInt(0)
    val `Event_scalaExec.plus` = (a : BigInt, b : BigInt) => a + b
  }
}

trait comm_monoid_add[A] extends ab_semigroup_add[A] with monoid_add[A] {
}
object comm_monoid_add {
  implicit def
    `Event_scalaExec.comm_monoid_add_integer` : comm_monoid_add[BigInt] = new
    comm_monoid_add[BigInt] {
    val `Event_scalaExec.zero` = BigInt(0)
    val `Event_scalaExec.plus` = (a : BigInt, b : BigInt) => a + b
  }
}

trait semiring_0[A]
  extends comm_monoid_add[A] with mult_zero[A] with semiring[A] {
}
object semiring_0 {
  implicit def `Event_scalaExec.semiring_0_integer` : semiring_0[BigInt] = new
    semiring_0[BigInt] {
    val `Event_scalaExec.times` = (a : BigInt, b : BigInt) => a * b
    val `Event_scalaExec.zero` = BigInt(0)
    val `Event_scalaExec.plus` = (a : BigInt, b : BigInt) => a + b
  }
}

trait monoid_mult[A] extends semigroup_mult[A] with power[A] {
}
object monoid_mult {
  implicit def `Event_scalaExec.monoid_mult_integer` : monoid_mult[BigInt] = new
    monoid_mult[BigInt] {
    val `Event_scalaExec.one` = one_integera
    val `Event_scalaExec.times` = (a : BigInt, b : BigInt) => a * b
  }
}

trait semiring_numeral[A]
  extends monoid_mult[A] with numeral[A] with semiring[A] {
}
object semiring_numeral {
  implicit def
    `Event_scalaExec.semiring_numeral_integer` : semiring_numeral[BigInt] = new
    semiring_numeral[BigInt] {
    val `Event_scalaExec.plus` = (a : BigInt, b : BigInt) => a + b
    val `Event_scalaExec.one` = one_integera
    val `Event_scalaExec.times` = (a : BigInt, b : BigInt) => a * b
  }
}

trait zero_neq_one[A] extends one[A] with zero[A] {
}
object zero_neq_one {
  implicit def `Event_scalaExec.zero_neq_one_integer` : zero_neq_one[BigInt] =
    new zero_neq_one[BigInt] {
    val `Event_scalaExec.zero` = BigInt(0)
    val `Event_scalaExec.one` = one_integera
  }
}

trait semiring_1[A]
  extends semiring_numeral[A] with semiring_0[A] with zero_neq_one[A] {
}
object semiring_1 {
  implicit def `Event_scalaExec.semiring_1_integer` : semiring_1[BigInt] = new
    semiring_1[BigInt] {
    val `Event_scalaExec.zero` = BigInt(0)
    val `Event_scalaExec.one` = one_integera
    val `Event_scalaExec.times` = (a : BigInt, b : BigInt) => a * b
    val `Event_scalaExec.plus` = (a : BigInt, b : BigInt) => a + b
  }
}

abstract sealed class natural
final case class Nata(a : BigInt) extends natural

def integer_of_natural(x0 : natural) : BigInt = x0 match {
  case Nata(x) => x
}

def plus_naturala(m : natural, n : natural) : natural =
  Nata(integer_of_natural(m) + integer_of_natural(n))

def zero_naturala : natural = Nata(BigInt(0))

abstract sealed class channelsa
final case class beoutchannel_rep() extends channelsa

def enum_channelsc : List[channelsa] = List(beoutchannel_rep())

def enum_all_channelsa(p : channelsa => Boolean) : Boolean =
  list_all[channelsa](p, enum_channelsc)

def enum_ex_channelsa(p : channelsa => Boolean) : Boolean =
  list_ex[channelsa](p, enum_channelsc)

def equal_channelsc(x0 : channelsa, x1 : channelsa) : Boolean = (x0, x1) match {
  case (beoutchannel_rep(), beoutchannel_rep()) => true
}

def chandom_channelsa(a : myself[channelsa]) : set[channel] =
  insert[channel](CH(List(Chara(false, true, false, false, false, true, true,
                                 false),
                           Chara(true, false, true, false, false, true, true,
                                  false),
                           Chara(true, true, true, true, false, false, true,
                                  false),
                           Chara(true, false, true, false, true, true, true,
                                  false),
                           Chara(false, false, true, false, true, true, true,
                                  false),
                           Chara(true, true, false, false, false, false, true,
                                  false),
                           Chara(false, false, false, true, false, true, true,
                                  false),
                           Chara(true, false, false, false, false, true, true,
                                  false),
                           Chara(false, true, true, true, false, true, true,
                                  false),
                           Chara(false, true, true, true, false, true, true,
                                  false),
                           Chara(true, false, true, false, false, true, true,
                                  false),
                           Chara(false, false, true, true, false, true, true,
                                  false),
                           Chara(true, true, true, true, true, false, true,
                                  false),
                           Chara(false, true, false, false, true, true, true,
                                  false),
                           Chara(true, false, true, false, false, true, true,
                                  false),
                           Chara(false, false, false, false, true, true, true,
                                  false)),
                      Ttlive(), Tboolevent()),
                   bot_set[channel])

def Rep_channelsc(x0 : channelsa) : channel = x0 match {
  case beoutchannel_rep() =>
    CH(List(Chara(false, true, false, false, false, true, true, false),
             Chara(true, false, true, false, false, true, true, false),
             Chara(true, true, true, true, false, false, true, false),
             Chara(true, false, true, false, true, true, true, false),
             Chara(false, false, true, false, true, true, true, false),
             Chara(true, true, false, false, false, false, true, false),
             Chara(false, false, false, true, false, true, true, false),
             Chara(true, false, false, false, false, true, true, false),
             Chara(false, true, true, true, false, true, true, false),
             Chara(false, true, true, true, false, true, true, false),
             Chara(true, false, true, false, false, true, true, false),
             Chara(false, false, true, true, false, true, true, false),
             Chara(true, true, true, true, true, false, true, false),
             Chara(false, true, false, false, true, true, true, false),
             Chara(true, false, true, false, false, true, true, false),
             Chara(false, false, false, false, true, true, true, false)),
        Ttlive(), Tboolevent())
}

def Abs_channelsa(x0 : channel) : channelsa = x0 match {
  case CH(List(Chara(false, true, false, false, false, true, true, false),
                Chara(true, false, true, false, false, true, true, false),
                Chara(true, true, true, true, false, false, true, false),
                Chara(true, false, true, false, true, true, true, false),
                Chara(false, false, true, false, true, true, true, false),
                Chara(true, true, false, false, false, false, true, false),
                Chara(false, false, false, true, false, true, true, false),
                Chara(true, false, false, false, false, true, true, false),
                Chara(false, true, true, true, false, true, true, false),
                Chara(false, true, true, true, false, true, true, false),
                Chara(true, false, true, false, false, true, true, false),
                Chara(false, false, true, true, false, true, true, false),
                Chara(true, true, true, true, true, false, true, false),
                Chara(false, true, false, false, true, true, true, false),
                Chara(true, false, true, false, false, true, true, false),
                Chara(false, false, false, false, true, true, true, false)),
           Ttlive(), Tboolevent())
    => beoutchannel_rep()
}

abstract sealed class tstimed[A]
final case class TSTIMEDA[A](a : A) extends tstimed[A]

def enum_all_tstimed[A : one_chan : enuma](p : (tstimed[A]) =>
         Boolean) : Boolean
  =
  enum_all[A](((c : A) => p(TSTIMEDA[A](c))))

def enum_ex_tstimed[A : one_chan : enuma](p : (tstimed[A]) => Boolean) : Boolean
  =
  enum_ex[A](((c : A) => p(TSTIMEDA[A](c))))

def map[A, B](f : A => B, x1 : List[A]) : List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x21 :: x22) => f(x21) :: map[A, B](f, x22)
}

def enum_tstimeda[A : one_chan : enuma] : List[tstimed[A]] =
  map[A, tstimed[A]](((a : A) => TSTIMEDA[A](a)), enuma[A])

def equal_tstimeda[A : one_chan : equal](x0 : tstimed[A],
  x1 : tstimed[A]) : Boolean
  =
  (x0, x1) match {
  case (TSTIMEDA(x), TSTIMEDA(ya)) => eq[A](x, ya)
}

def changetimetype(tt : timetype, x1 : channel) : channel = (tt, x1) match {
  case (tt, CH(name, uu, p)) => CH(name, tt, p)
}

def image[A, B](f : A => B, x1 : set[A]) : set[B] = (f, x1) match {
  case (f, seta(xs)) => seta[B](map[A, B](f, xs))
}

def chandom_tstimed[A : one_chan](uu : myself[tstimed[A]]) : set[channel] =
  image[channel,
         channel](((a : channel) => changetimetype(Ttfin(), a)),
                   chandom[A](DUMMY[A]()))

def member[A : equal](x : A, xa1 : set[A]) : Boolean = (x, xa1) match {
  case (x, coset(xs)) => ! (membera[A](xs, x))
  case (x, seta(xs)) => membera[A](xs, x)
}

def Rep_tstimeda[A : one_chan](x0 : tstimed[A]) : channel = x0 match {
  case TSTIMEDA(cs) =>
    (member[channel](Rep[A](cs), chandom[A](DUMMY[A]())) match {
      case true => changetimetype(Ttfin(), Rep[A](cs)) case false => Rep[A](cs)
      })
}

def less_eq_set[A : equal](a : set[A], b : set[A]) : Boolean = (a, b) match {
  case (coset(Nil), seta(Nil)) => false
  case (a, coset(ys)) => list_all[A](((y : A) => ! (member[A](y, a))), ys)
  case (seta(xs), b) => list_all[A](((x : A) => member[A](x, b)), xs)
}

def equal_set[A : equal](a : set[A], b : set[A]) : Boolean =
  less_eq_set[A](a, b) && less_eq_set[A](b, a)

def cname(x0 : channel) : List[char] = x0 match {
  case CH(name, uu, uv) => name
}

def top_set[A] : set[A] = coset[A](Nil)

def cmsgt(x0 : msgtype) : set[msg] = x0 match {
  case Tboolevent() =>
    image[Boolean, msg](((a : Boolean) => booleventconstr(a)), top_set[Boolean])
  case Tboolsync() =>
    image[Boolean, msg](((a : Boolean) => boolsyncconstr(a)), top_set[Boolean])
  case Tnatevent() =>
    image[nat, msg](((a : nat) => nateventconstr(a)), top_set[nat])
  case Tnatsync() =>
    image[nat, msg](((a : nat) => natsyncconstr(a)), top_set[nat])
  case Tstringevent() =>
    image[List[char],
           msg](((a : List[char]) => stringeventconstr(a)), top_set[List[char]])
  case Tstringsync() =>
    image[List[char],
           msg](((a : List[char]) => stringsyncconstr(a)), top_set[List[char]])
  case Tnone() => bot_set[msg]
}

def cmsg(x0 : channel) : set[msg] = x0 match {
  case CH(uu, uv, mt) => cmsgt(mt)
}

def enum_the[A](a : A => Boolean) : A = sys.error("Enum.enum_the")

def filter[A](p : A => Boolean, x1 : List[A]) : List[A] = (p, x1) match {
  case (p, Nil) => Nil
  case (p, x :: xs) =>
    (p(x) match { case true => x :: filter[A](p, xs)
      case false => filter[A](p, xs) })
}

def The[A : enuma](p : A => Boolean) : A =
  (filter[A](p, enuma[A]) match {
     case Nil => enum_the[A](p)
     case List(x) => x
     case _ :: _ :: _ => enum_the[A](p)
   })

def Abs_tstimed[A : one_chan : enuma](cs : channel) : tstimed[A] =
  (member[channel](cs, chandom_tstimed[A](DUMMY[tstimed[A]]())) match {
    case true => TSTIMEDA[A](The[A](((a : A) =>
                                      equal_lista[char](cname(Rep[A](a)),
                 cname(cs)) &&
equal_set[msg](cmsg(Rep[A](a)), cmsg(cs)))))
    case false => TSTIMEDA[A](Abs[A](cs)) })

trait tschan[A] extends tchan[A] {
}
object tschan {
  implicit def
    `Event_scalaExec.tschan_tstimed`[A : one_chan : enuma] : tschan[tstimed[A]]
    = new tschan[tstimed[A]] {
    val `Event_scalaExec.Rep` = (a : tstimed[A]) => Rep_tstimeda[A](a)
    val `Event_scalaExec.Abs` = (a : channel) => Abs_tstimed[A](a)
    val `Event_scalaExec.chandom` = (a : myself[tstimed[A]]) =>
      chandom_tstimed[A](a)
  }
}

abstract sealed class msgwithchan[A]
final case class Abs_msgwithchan[A](a : (A, msg)) extends msgwithchan[A]

def equal_msgwithchana[A : chan](ec1 : msgwithchan[A],
                                  ec2 : msgwithchan[A]) : Boolean
  =
  equal_msgwithchana[A](ec1, ec2)

abstract sealed class typerepa
final case class Typerepb(a : String, b : List[typerepa]) extends typerepa

abstract sealed class Substate
final case class state_s() extends Substate
final case class state_t() extends Substate

abstract sealed class State
final case class Stateconstr(a : Substate) extends State

abstract sealed class itself[A]
final case class typea[A]() extends itself[A]

def typerep_statea(t : itself[State]) : typerepa =
  Typerepb("MultipleParameters_States.State", Nil)

trait typerep[A] {
  val `Event_scalaExec.typerep` : (itself[A]) => typerepa
}
def typerep[A](a : itself[A])(implicit A: typerep[A]) : typerepa =
  A.`Event_scalaExec.typerep`(a)
object typerep {
  implicit def `Event_scalaExec.typerep_state` : typerep[State] = new
    typerep[State] {
    val `Event_scalaExec.typerep` = (a : itself[State]) => typerep_statea(a)
  }
}

def one_natural : natural = Nata(BigInt(1))

def scomp[A, B, C, D](f : A => (B, C), g : B => C => D) : A => D =
  ((x : A) => {
                val (a, b) = f(x) : ((B, C));
                (g(a))(b)
              })

def id[A] : A => A = ((x : A) => x)

def collapse[A, B](f : A => (A => (B, A), A)) : A => (B, A) =
  scomp[A, A => (B, A), A, (B, A)](f, id[A => (B, A)])

abstract sealed class term
final case class Const(a : String, b : typerepa) extends term
final case class App(a : term, b : term) extends term
final case class Abs(a : String, b : typerepa, c : term) extends term
final case class Free(a : String, b : typerepa) extends term

def foldr[A, B](f : A => B => B, x1 : List[A]) : B => B = (f, x1) match {
  case (f, Nil) => id[B]
  case (f, x :: xs) => comp[B, B, B](f(x), foldr[A, B](f, xs))
}

def sum_list[A : monoid_add](xs : List[A]) : A =
  (foldr[A, A](((a : A) => (b : A) => plus[A](a, b)), xs)).apply(zero[A])

def fst[A, B](x0 : (A, B)) : A = x0 match {
  case (x1, x2) => x1
}

def apsnd[A, B, C](f : A => B, x1 : (C, A)) : (C, B) = (f, x1) match {
  case (f, (x, y)) => (x, f(y))
}

def divmod_integer(k : BigInt, l : BigInt) : (BigInt, BigInt) =
  (k == BigInt(0) match { case true => (BigInt(0), BigInt(0))
    case false => (BigInt(0) < l match {
                    case true => (BigInt(0) < k match {
                                   case true => ((k: BigInt) => (l: BigInt) =>
          l == 0 match { case true => (BigInt(0), k) case false => (k.abs /% l.abs) }).apply(k).apply(l)
                                   case false => {
           val (r, s) =
             ((k: BigInt) => (l: BigInt) =>
               l == 0 match { case true => (BigInt(0), k) case false => (k.abs /% l.abs) }).apply(k).apply(l) : ((BigInt,
                                  BigInt));
           (s == BigInt(0) match { case true => ((- r), BigInt(0))
             case false => ((- r) - BigInt(1), l - s) })
         }
                                   })
                    case false => (l == BigInt(0) match {
                                    case true => (BigInt(0), k)
                                    case false => apsnd[BigInt, BigInt,
                 BigInt](((a : BigInt) => (- a)),
                          (k < BigInt(0) match {
                            case true => ((k: BigInt) => (l: BigInt) =>
   l == 0 match { case true => (BigInt(0), k) case false => (k.abs /% l.abs) }).apply(k).apply(l)
                            case false => {
    val (r, s) =
      ((k: BigInt) => (l: BigInt) =>
        l == 0 match { case true => (BigInt(0), k) case false => (k.abs /% l.abs) }).apply(k).apply(l) : ((BigInt,
                           BigInt));
    (s == BigInt(0) match { case true => ((- r), BigInt(0))
      case false => ((- r) - BigInt(1), (- l) - s) })
  }
                            }))
                                    })
                    })
    })

def snd[A, B](x0 : (A, B)) : B = x0 match {
  case (x1, x2) => x2
}

def modulo_integer(k : BigInt, l : BigInt) : BigInt =
  snd[BigInt, BigInt](divmod_integer(k, l))

def modulo_natural(m : natural, n : natural) : natural =
  Nata(modulo_integer(integer_of_natural(m), integer_of_natural(n)))

def times_natural(m : natural, n : natural) : natural =
  Nata(integer_of_natural(m) * integer_of_natural(n))

def max[A : ord](a : A, b : A) : A =
  (less_eq[A](a, b) match { case true => b case false => a })

def natural_of_integer(k : BigInt) : natural = Nata(max[BigInt](BigInt(0), k))

def minus_natural(m : natural, n : natural) : natural =
  Nata(max[BigInt](BigInt(0), integer_of_natural(m) - integer_of_natural(n)))

def equal_natural(m : natural, n : natural) : Boolean =
  integer_of_natural(m) == integer_of_natural(n)

def iterate[A, B](k : natural, f : A => B => (A, B), x : A) : B => (A, B) =
  (equal_natural(k, zero_naturala) match { case true => ((a : B) => (x, a))
    case false => scomp[B, A, B,
                         (A, B)](f(x),
                                  ((a : A) =>
                                    iterate[A,
     B](minus_natural(k, one_natural), f, a)))
    })

def divide_integer(k : BigInt, l : BigInt) : BigInt =
  fst[BigInt, BigInt](divmod_integer(k, l))

def divide_natural(m : natural, n : natural) : natural =
  Nata(divide_integer(integer_of_natural(m), integer_of_natural(n)))

def less_natural(m : natural, n : natural) : Boolean =
  integer_of_natural(m) < integer_of_natural(n)

def minus_shift(r : natural, k : natural, l : natural) : natural =
  (less_natural(k, l) match { case true => minus_natural(plus_naturala(r, k), l)
    case false => minus_natural(k, l) })

def next(x0 : (natural, natural)) : (natural, (natural, natural)) = x0 match {
  case (v, w) =>
    {
      val k = divide_natural(v, natural_of_integer(BigInt(53668))) : natural
      val va =
        minus_shift(natural_of_integer(BigInt(2147483563)),
                     times_natural(modulo_natural(v,
           natural_of_integer(BigInt(53668))),
                                    natural_of_integer(BigInt(40014))),
                     times_natural(k, natural_of_integer(BigInt(12211)))) : natural
      val l = divide_natural(w, natural_of_integer(BigInt(52774))) : natural
      val wa =
        minus_shift(natural_of_integer(BigInt(2147483399)),
                     times_natural(modulo_natural(w,
           natural_of_integer(BigInt(52774))),
                                    natural_of_integer(BigInt(40692))),
                     times_natural(l, natural_of_integer(BigInt(3791)))) : natural
      val z =
        plus_naturala(minus_shift(natural_of_integer(BigInt(2147483562)), va,
                                   plus_naturala(wa, one_natural)),
                       one_natural) : natural;
      (z, (va, wa))
    }
}

def less_eq_natural(m : natural, n : natural) : Boolean =
  integer_of_natural(m) <= integer_of_natural(n)

def log(b : natural, i : natural) : natural =
  (less_eq_natural(b, one_natural) || less_natural(i, b) match {
    case true => one_natural
    case false => plus_naturala(one_natural, log(b, divide_natural(i, b))) })

def range(k : natural) : ((natural, natural)) => (natural, (natural, natural)) =
  scomp[(natural, natural), natural, (natural, natural),
         (natural,
           (natural,
             natural))](iterate[natural,
                                 (natural,
                                   natural)](log(natural_of_integer(BigInt(2147483561)),
          k),
      ((l : natural) =>
        scomp[(natural, natural), natural, (natural, natural),
               (natural,
                 (natural,
                   natural))](((a : (natural, natural)) => next(a)),
                               ((v : natural) =>
                                 ((a : (natural, natural)) =>
                                   (plus_naturala(v,
           times_natural(l, natural_of_integer(BigInt(2147483561)))),
                                     a))))),
      one_natural),
                         ((v : natural) =>
                           ((a : (natural, natural)) =>
                             (modulo_natural(v, k), a))))

def pick[A](x0 : List[(natural, A)], i : natural) : A = (x0, i) match {
  case (x :: xs, i) =>
    (less_natural(i, fst[natural, A](x)) match { case true => snd[natural, A](x)
      case false => pick[A](xs, minus_natural(i, fst[natural, A](x))) })
}

def select_weight[A](xs : List[(natural,
                                 A)]) : ((natural, natural)) =>
  (A, (natural, natural))
  =
  scomp[(natural, natural), natural, (natural, natural),
         (A, (natural,
               natural))](range(sum_list[natural](map[(natural, A),
               natural](((a : (natural, A)) => fst[natural, A](a)), xs))),
                           ((k : natural) =>
                             ((a : (natural, natural)) => (pick[A](xs, k), a))))

def random_aux_substate(i : natural, j : natural,
                         s : (natural,
                               natural)) : ((Substate, Unit => term),
     (natural, natural))
  =
  (collapse[(natural, natural),
             (Substate,
               Unit =>
                 term)](select_weight[((natural, natural)) =>
((Substate, Unit => term),
  (natural,
    natural))](List((one_natural,
                      ((a : (natural, natural)) =>
                        ((state_s(),
                           ((_ : Unit) =>
                             Const("MultipleParameters_States.Substate.state__S",
                                    Typerepb("MultipleParameters_States.Substate",
      Nil)))),
                          a))),
                     (one_natural,
                       ((a : (natural, natural)) =>
                         ((state_t(),
                            ((_ : Unit) =>
                              Const("MultipleParameters_States.Substate.state__T",
                                     Typerepb("MultipleParameters_States.Substate",
       Nil)))),
                           a))))))).apply(s)

def random_substate(i : natural) : ((natural, natural)) =>
                                     ((Substate, Unit => term),
                                       (natural, natural))
  =
  ((a : (natural, natural)) => random_aux_substate(i, i, a))

def valapp[A, B](x0 : (A => B, Unit => term),
                  x1 : (A, Unit => term)) : (B, Unit => term)
  =
  (x0, x1) match {
  case ((f, tf), (x, tx)) => (f(x), ((_ : Unit) => App(tf(()), tx(()))))
}

def random_aux_state(i : natural, j : natural,
                      s : (natural,
                            natural)) : ((State, Unit => term),
  (natural, natural))
  =
  (collapse[(natural, natural),
             (State,
               Unit =>
                 term)](select_weight[((natural, natural)) =>
((State, Unit => term),
  (natural,
    natural))](List((one_natural,
                      scomp[(natural, natural), (Substate, Unit => term),
                             (natural, natural),
                             ((State, Unit => term),
                               (natural,
                                 natural))](random_substate(j),
     ((x : (Substate, Unit => term)) =>
       ((a : (natural, natural)) =>
         (valapp[Substate,
                  State]((((aa : Substate) => Stateconstr(aa)),
                           ((_ : Unit) =>
                             Const("MultipleParameters_States.State.StateConstr",
                                    Typerepb("fun",
      List(Typerepb("MultipleParameters_States.Substate", Nil),
            Typerepb("MultipleParameters_States.State", Nil)))))),
                          x),
           a))))))))).apply(s)

def random_statea(i : natural) : ((natural, natural)) =>
                                   ((State, Unit => term), (natural, natural))
  =
  ((a : (natural, natural)) => random_aux_state(i, i, a))

trait random[A] extends typerep[A] {
  val `Event_scalaExec.random` : (natural, (natural, natural)) =>
                                   ((A, Unit => term), (natural, natural))
}
def random[A](a : natural,
               b : (natural,
                     natural))(implicit A: random[A]) : ((A, Unit => term),
                  (natural, natural))
  = A.`Event_scalaExec.random`(a, b)
object random {
  implicit def `Event_scalaExec.random_state` : random[State] = new
    random[State] {
    val `Event_scalaExec.random` = (a : natural, b : (natural, natural)) =>
      (random_statea(a)).apply(b)
    val `Event_scalaExec.typerep` = (a : itself[State]) => typerep_statea(a)
  }
}

abstract sealed class u[A]
final case class Ibottom[A]() extends u[A]
final case class Iup[A](a : A) extends u[A]

abstract sealed class eventwellstream[A]
final case class Abs_eventwellstream[A](a : stream[event[(A, msg)]]) extends
  eventwellstream[A]

abstract sealed class execautomaton_ext[A, B, C, D]
final case class execautomaton_exta[A, B, C,
                                     D](a : A => B => natural => (A, C),
 b : natural => (A, C), c : D)
  extends execautomaton_ext[A, B, C, D]

abstract sealed class listautomaton_ext[A, B, C, D]
final case class listautomaton_exta[A, B, C,
                                     D](a : A => B => List[(A, C)],
 b : List[(A, C)], c : D)
  extends listautomaton_ext[A, B, C, D]

abstract sealed class dautomaton_ext[A, B, C, D]
final case class dautomaton_exta[A, B, C,
                                  D](a : A => B => (A, C), b : (A, C), c : D)
  extends dautomaton_ext[A, B, C, D]

def nth[A](x0 : List[A], x1 : nat) : A = (x0, x1) match {
  case (x :: xs, Suc(n)) => nth[A](xs, n)
  case (x :: xs, zero_nat()) => x
}

def maps[A, B](f : A => List[B], x1 : List[A]) : List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x :: xs) => f(x) ++ maps[A, B](f, xs)
}

def nulla[A](x0 : List[A]) : Boolean = x0 match {
  case Nil => true
  case x :: xs => false
}

def rnd[A : random](seed : (natural, natural)) : A =
  fst[A, Unit =>
           term](fst[(A, Unit => term),
                      (natural,
                        natural)](random[A](natural_of_integer(BigInt(1000)),
     seed)))

def Rep_sbelem[A : chan](x0 : sbelem[A]) : Option[A => M] = x0 match {
  case Abs_sbelem(x) => x
}

def sbelem_none[A : chan] : sbelem[A] =
  Abs_sbelem[A]((equal_set[channel](chandom[A](DUMMY[A]()),
                                     bot_set[channel]) match {
                  case true => None
                  case false => Rep_sbelem[A](sys.error("undefined")) }))

def shd_nc[A : countable](x0 : stream[A]) : A = x0 match {
  case lscons_u_nc(a, b) => a
}

def equal_stream[A : countable : equal](a : stream[A], b : stream[A]) : Boolean
  =
  StreamEqual.streamequal[A](a, b)

def sbhdelemwell[A : chan : enuma](sb : sb[A]) : Boolean =
  All[A](((c : A) =>
           ! (equal_stream[M]((Rep_lsb[A](sb)).apply(c),
                               stream_bottom_nc[M]()))))

def shd_elem[A : chan : enuma](sb : sb[A]) : sbelem[A] =
  Abs_sbelem[A]((! (sbhdelemwell[A](sb)) match {
                  case true => Rep_sbelem[A](sys.error("undefined"))
                  case false => Some[A => M](((c : A) =>
       shd_nc[M]((Rep_lsb[A](sb)).apply(c))))
                  }))

def sbhdelem_h[A : chan : enuma](sb : sb[A]) : u[sbelem[A]] =
  (equal_set[channel](chandom[A](DUMMY[A]()), bot_set[channel]) match {
    case true => Iup[sbelem[A]](sbelem_none[A])
    case false => (! (sbhdelemwell[A](sb)) match {
                    case true => Ibottom[sbelem[A]]()
                    case false => Iup[sbelem[A]](shd_elem[A](sb)) })
    })

def sbhdelem[A : chan : enuma : equal](sb : sb[A]) : sbelem[A] =
  {
    val (Iup(sbElem)) = sbhdelem_h[A](sb) : (u[sbelem[A]]);
    sbElem
  }

def list2s[A : countable](x0 : List[A]) : stream[A] = x0 match {
  case Nil => stream_bottom_nc[A]()
  case a :: as => lscons_u_nc[A](a, list2s[A](as))
}

def m2list(x0 : M) : List[msg] = x0 match {
  case Timed(Tfin(ls)) => ls
  case Timed(Tlive(Eventmsg(e))) => List(e)
  case Timed(Tlive(Tick())) => Nil
  case Untimed(e) => List(e)
  case Timed(Tsyna(Tsynmsg(m))) => List(m)
  case Timed(Tsyna(Eps())) => Nil
  case Timed(Tonea(va)) => List(va)
}

def equal_substate(x0 : Substate, x1 : Substate) : Boolean = (x0, x1) match {
  case (state_s(), state_t()) => false
  case (state_t(), state_s()) => false
  case (state_t(), state_t()) => true
  case (state_s(), state_s()) => true
}

def guardt_0(x0 : Unit, x1 : State) : Boolean = (x0, x1) match {
  case ((), Stateconstr(s)) => equal_substate(s, state_s()) && true
}

def guardt_1(x0 : Unit, x1 : State) : Boolean = (x0, x1) match {
  case ((), Stateconstr(s)) => equal_substate(s, state_s()) && true
}

def guard_00(x0 : Unit, x1 : State, beInChannel_pattern : Boolean) : Boolean =
  (x0, x1, beInChannel_pattern) match {
  case ((), Stateconstr(s), beInChannel_pattern) =>
    equal_substate(s, state_s()) && equal_boola(beInChannel_pattern, false)
}

def guard_01(x0 : Unit, x1 : State, beInChannel_pattern : Boolean) : Boolean =
  (x0, x1, beInChannel_pattern) match {
  case ((), Stateconstr(s), beInChannel_pattern) =>
    equal_substate(s, state_s()) && equal_boola(beInChannel_pattern, true)
}

def listeventwrapper[A, B,
                      C](f : (event[A]) => List[(B, List[C])],
                          x1 : event[A]) : List[(B, List[event[C]])]
  =
  (f, x1) match {
  case (f, Tick()) =>
    map[(B, List[C]),
         (B, List[event[C]])](((a : (B, List[C])) =>
                                apsnd[List[C], List[event[C]],
                                       B](((ls : List[C]) =>
    Tick[C]() :: map[C, event[C]](((aa : C) => Eventmsg[C](aa)), ls)),
   a)),
                               f(Tick[A]()))
  case (f, Eventmsg(v)) =>
    map[(B, List[C]),
         (B, List[event[C]])](((a : (B, List[C])) =>
                                apsnd[List[C], List[event[C]],
                                       B](((aa : List[C]) =>
    map[C, event[C]](((ab : C) => Eventmsg[C](ab)), aa)),
   a)),
                               f(Eventmsg[A](v)))
}

def Rep_msgwithchan[A : chan](x0 : msgwithchan[A]) : (A, msg) = x0 match {
  case Abs_msgwithchan(x) => x
}

def efilter_nc[A : countable](p : A => Boolean,
                               x1 : stream[event[A]]) : stream[event[A]]
  =
  (p, x1) match {
  case (p, lscons_u_nc(Tick(), as)) =>
    sconc_nc[event[A]](sup[event[A]](Tick[A]()), efilter_nc[A](p, as))
  case (p, lscons_u_nc(Eventmsg(a), as)) =>
    (p(a) match {
      case true => sconc_nc[event[A]](sup[event[A]](Eventmsg[A](a)),
                                       efilter_nc[A](p, as))
      case false => efilter_nc[A](p, as) })
  case (p, stream_bottom_nc()) => stream_bottom_nc[event[A]]()
}

def map_event[A, B](f : A => B, x1 : event[A]) : event[B] = (f, x1) match {
  case (f, Eventmsg(x1)) => Eventmsg[B](f(x1))
  case (f, Tick()) => Tick[B]()
}

def emap_nc[A : countable,
             B : countable](f : A => B, s : stream[event[A]]) : stream[event[B]]
  =
  smap_nc[event[A], event[B]](((a : event[A]) => map_event[A, B](f, a)), s)

def usplit_nc[A : echan : finite : equal](s : stream[event[msgwithchan[A]]]) : sb[A]
  =
  Abs_lsb[A]((equal_set[channel](chandom[A](DUMMY[A]()),
                                  bot_set[channel]) match {
               case true => ((_ : A) => stream_bottom_nc[M]())
               case false => ((c : A) =>
                               smap_nc[event[msg],
M](comp[M_timed, M,
         event[msg]](((a : M_timed) => Timed(a)),
                      ((a : event[msg]) => Tlive(a))),
    emap_nc[(A, msg),
             msg](((a : (A, msg)) => snd[A, msg](a)),
                   efilter_nc[(A, msg)](((a : (A, msg)) =>
  {
    val (x, _) = a : ((A, msg));
    eq[A](x, c)
  }),
 emap_nc[msgwithchan[A],
          (A, msg)](((a : msgwithchan[A]) => Rep_msgwithchan[A](a)), s)))))
               }))

def usplit[A : echan : enuma : equal] : cfun[stream[event[msgwithchan[A]]],
      sb[A]]
  =
  Abs_cfun[stream[event[msgwithchan[A]]],
            sb[A]](((a : stream[event[msgwithchan[A]]]) => usplit_nc[A](a)))

def beoutchannelconstr(xa : Boolean) : msgwithchan[channelsa] =
  Abs_msgwithchan[channelsa]((beoutchannel_rep(), booleventconstr(xa)))

def executableexpression_01(x0 : Unit, x1 : State,
                             beInChannel_pattern : Boolean) : List[(State,
                             List[msgwithchan[channelsa]])]
  =
  (x0, x1, beInChannel_pattern) match {
  case ((), Stateconstr(s), beInChannel_pattern) =>
    List((Stateconstr(state_s()), List(beoutchannelconstr(true))))
}

def executabletransitionh_01(x0 : Unit, x1 : State,
                              beInChannel_pattern : Boolean) : List[(State,
                              List[msgwithchan[channelsa]])]
  =
  (x0, x1, beInChannel_pattern) match {
  case ((), Stateconstr(s), beInChannel_pattern) =>
    (guard_01((), Stateconstr(s), beInChannel_pattern) match {
      case true => executableexpression_01((), Stateconstr(s),
    beInChannel_pattern)
      case false => Nil })
}

def executableexpression_00(x0 : Unit, x1 : State,
                             beInChannel_pattern : Boolean) : List[(State,
                             List[msgwithchan[channelsa]])]
  =
  (x0, x1, beInChannel_pattern) match {
  case ((), Stateconstr(s), beInChannel_pattern) =>
    List((Stateconstr(state_s()), List(beoutchannelconstr(false))))
}

def executabletransitionh_00(x0 : Unit, x1 : State,
                              beInChannel_pattern : Boolean) : List[(State,
                              List[msgwithchan[channelsa]])]
  =
  (x0, x1, beInChannel_pattern) match {
  case ((), Stateconstr(s), beInChannel_pattern) =>
    (guard_00((), Stateconstr(s), beInChannel_pattern) match {
      case true => executableexpression_00((), Stateconstr(s),
    beInChannel_pattern)
      case false => Nil })
}

def executableeventtransition(para : Unit, state : State,
                               x2 : (channels,
                                      msg)) : List[(State,
             List[msgwithchan[channelsa]])]
  =
  (para, state, x2) match {
  case (para, state, (beinchannel_rep(), booleventconstr(beInChannel_pattern)))
    => executabletransitionh_00(para, state, beInChannel_pattern) ++
         executabletransitionh_01(para, state, beInChannel_pattern)
}

def eventtransition(p : Unit, s : State,
                     i : (channels,
                           msg)) : List[(State, List[msgwithchan[channelsa]])]
  =
  (nulla[(State,
           List[msgwithchan[channelsa]])](executableeventtransition(p, s,
                             i)) match {
    case true => List((s, Nil)) case false => executableeventtransition(p, s, i)
    })

def executableexpressiont_1(x0 : Unit,
                             x1 : State) : List[(State,
          List[msgwithchan[channelsa]])]
  =
  (x0, x1) match {
  case ((), Stateconstr(s)) =>
    List((Stateconstr(state_s()), List(beoutchannelconstr(true))))
}

def executabletransitionth_1(x0 : Unit,
                              x1 : State) : List[(State,
           List[msgwithchan[channelsa]])]
  =
  (x0, x1) match {
  case ((), Stateconstr(s)) =>
    (guardt_1((), Stateconstr(s)) match {
      case true => executableexpressiont_1((), Stateconstr(s)) case false => Nil
      })
}

def executableexpressiont_0(x0 : Unit,
                             x1 : State) : List[(State,
          List[msgwithchan[channelsa]])]
  =
  (x0, x1) match {
  case ((), Stateconstr(s)) =>
    List((Stateconstr(state_s()), List(beoutchannelconstr(false))))
}

def executabletransitionth_0(x0 : Unit,
                              x1 : State) : List[(State,
           List[msgwithchan[channelsa]])]
  =
  (x0, x1) match {
  case ((), Stateconstr(s)) =>
    (guardt_0((), Stateconstr(s)) match {
      case true => executableexpressiont_0((), Stateconstr(s)) case false => Nil
      })
}

def executableticktransition(para : Unit,
                              state : State) : List[(State,
              List[msgwithchan[channelsa]])]
  =
  executabletransitionth_0(para, state) ++ executabletransitionth_1(para, state)

def ticktransition(p : Unit,
                    s : State) : List[(State, List[msgwithchan[channelsa]])]
  =
  (nulla[(State,
           List[msgwithchan[channelsa]])](executableticktransition(p,
                            s)) match {
    case true => List((s, Nil)) case false => executableticktransition(p, s) })

def ndatransition(p : Unit, s : State,
                   x2 : event[(channels,
                                msg)]) : List[(State,
        List[msgwithchan[channelsa]])]
  =
  (p, s, x2) match {
  case (p, s, Tick()) => ticktransition(p, s)
  case (p, s, Eventmsg(m)) => eventtransition(p, s, m)
}

def Rep_cfun[B : cpo, A : cpo](x0 : cfun[B, A]) : B => A = x0 match {
  case Abs_cfun(x) => x
}

def transition(p : Unit,
                s : State) : (event[(channels, msg)]) =>
                               List[(State, sb[channelsa])]
  =
  comp[List[(State, List[event[msgwithchan[channelsa]]])],
        List[(State, sb[channelsa])],
        event[(channels,
                msg)]](((a : List[(State, List[event[msgwithchan[channelsa]]])])
                          =>
                         map[(State, List[event[msgwithchan[channelsa]]]),
                              (State,
                                sb[channelsa])](((aa : (State,
                 List[event[msgwithchan[channelsa]]]))
           =>
          apsnd[List[event[msgwithchan[channelsa]]], sb[channelsa],
                 State](comp[stream[event[msgwithchan[channelsa]]],
                              sb[channelsa],
                              List[event[msgwithchan[channelsa]]]](Rep_cfun[stream[event[msgwithchan[channelsa]]],
                                     sb[channelsa]](usplit[channelsa]),
                            ((ab : List[event[msgwithchan[channelsa]]]) =>
                              list2s[event[msgwithchan[channelsa]]](ab))),
                         aa)),
         a)),
                        ((a : event[(channels, msg)]) =>
                          listeventwrapper[(channels, msg), State,
    msgwithchan[channelsa]](((aa : event[(channels, msg)]) =>
                              ndatransition(p, s, aa)),
                             a)))

def executableinitialconfigs : Unit =>
                                 List[(State, List[msgwithchan[channelsa]])]
  =
  ((a : Unit) => {
                   val () = a : Unit;
                   List((Stateconstr(state_s()), Nil))
                 })

def configc(p : Unit) : List[(State, List[msgwithchan[channelsa]])] =
  (nulla[(State,
           List[msgwithchan[channelsa]])](executableinitialconfigs.apply(p)) match {
    case true => List((rnd[State]((natural_of_integer(BigInt(2)),
                                    natural_of_integer(BigInt(3)))),
                        Nil))
    case false => executableinitialconfigs.apply(p) })

def config(p : Unit) : List[(State, sb[channelsa])] =
  (true match {
    case true => map[(State, List[event[msgwithchan[channelsa]]]),
                      (State,
                        sb[channelsa])](((a : (State,
        List[event[msgwithchan[channelsa]]]))
   =>
  apsnd[List[event[msgwithchan[channelsa]]], sb[channelsa],
         State](comp[stream[event[msgwithchan[channelsa]]], sb[channelsa],
                      List[event[msgwithchan[channelsa]]]](Rep_cfun[stream[event[msgwithchan[channelsa]]],
                             sb[channelsa]](usplit[channelsa]),
                    ((aa : List[event[msgwithchan[channelsa]]]) =>
                      list2s[event[msgwithchan[channelsa]]](aa))),
                 a)),
 map[(State, List[msgwithchan[channelsa]]),
      (State,
        List[event[msgwithchan[channelsa]]])](((a : (State,
              List[msgwithchan[channelsa]]))
         =>
        apsnd[List[msgwithchan[channelsa]], List[event[msgwithchan[channelsa]]],
               State](((ls : List[msgwithchan[channelsa]]) =>
                        map[msgwithchan[channelsa],
                             event[msgwithchan[channelsa]]](((aa : msgwithchan[channelsa])
                       =>
                      Eventmsg[msgwithchan[channelsa]](aa)),
                     ls) ++
                          List(Tick[msgwithchan[channelsa]]())),
                       a)),
       configc(p)))
    case false => map[(State, List[event[msgwithchan[channelsa]]]),
                       (State,
                         sb[channelsa])](((a : (State,
         List[event[msgwithchan[channelsa]]]))
    =>
   apsnd[List[event[msgwithchan[channelsa]]], sb[channelsa],
          State](comp[stream[event[msgwithchan[channelsa]]], sb[channelsa],
                       List[event[msgwithchan[channelsa]]]](Rep_cfun[stream[event[msgwithchan[channelsa]]],
                              sb[channelsa]](usplit[channelsa]),
                     ((aa : List[event[msgwithchan[channelsa]]]) =>
                       list2s[event[msgwithchan[channelsa]]](aa))),
                  a)),
  map[(State, List[msgwithchan[channelsa]]),
       (State,
         List[event[msgwithchan[channelsa]]])](((a : (State,
               List[msgwithchan[channelsa]]))
          =>
         apsnd[List[msgwithchan[channelsa]],
                List[event[msgwithchan[channelsa]]],
                State](((aa : List[msgwithchan[channelsa]]) =>
                         map[msgwithchan[channelsa],
                              event[msgwithchan[channelsa]]](((ab : msgwithchan[channelsa])
                        =>
                       Eventmsg[msgwithchan[channelsa]](ab)),
                      aa)),
                        a)),
        configc(p)))
    })

def laut(p : Unit) : listautomaton_ext[State, event[(channels, msg)],
sb[channelsa], Unit]
  =
  listautomaton_exta[State, event[(channels, msg)], sb[channelsa],
                      Unit](((a : State) => transition(p, a)), config(p), ())

def gen_length[A](n : nat, x1 : List[A]) : nat = (n, x1) match {
  case (n, x :: xs) => gen_length[A](Suc(n), xs)
  case (n, Nil) => n
}

def Rep_eventwellstream[A : chan : countable](x0 : eventwellstream[A]) : stream[event[(A,
        msg)]]
  =
  x0 match {
  case Abs_eventwellstream(x) => x
}

def dautinitconfig[A, B, C : conc, D](x0 : dautomaton_ext[A, B, C, D]) : (A, C)
  =
  x0 match {
  case dautomaton_exta(dautTransition, dautInitConfig, more) => dautInitConfig
}

def dauttransition[A, B, C : conc,
                    D](x0 : dautomaton_ext[A, B, C, D]) : A => B => (A, C)
  =
  x0 match {
  case dautomaton_exta(dautTransition, dautInitConfig, more) => dautTransition
}

def execstatesem_nc[A, B : countable,
                     C : bot_nc : conc](aut : dautomaton_ext[A, B, C, Unit],
 s : A, x2 : stream[B]) : C
  =
  (aut, s, x2) match {
  case (aut, s, lscons_u_nc(a, rt)) =>
    (Rep_cfun[C, C](conc[C](snd[A, C]((dauttransition[A, B, C,
               Unit](aut)).apply(s).apply(a)))))(implicitly[bot_nc[C]],
          implicitly[bot_nc[C]]).apply(execstatesem_nc[A, B,
                C](aut, fst[A, C]((dauttransition[A, B, C,
           Unit](aut)).apply(s).apply(a)),
                    rt))
  case (aut, s, stream_bottom_nc()) => bot_nc[C]
}

def execsem_nc[A, B : countable,
                C : bot_nc : conc](aut : dautomaton_ext[A, B, C, Unit],
                                    s : stream[B]) : C
  =
  (Rep_cfun[C, C](conc[C](snd[A, C](dautinitconfig[A, B, C,
            Unit](aut)))))(implicitly[bot_nc[C]],
                            implicitly[bot_nc[C]]).apply(execstatesem_nc[A, B,
                                  C](aut, fst[A,
       C](dautinitconfig[A, B, C, Unit](aut)),
                                      s))

def listmerge[A](x0 : List[A], b : List[A]) : List[List[A]] = (x0, b) match {
  case (Nil, b) => List(b)
  case (v :: va, Nil) => List(v :: va)
  case (a :: as, b :: bs) =>
    map[List[A],
         List[A]](((ba : List[A]) => a :: ba), listmerge[A](as, b :: bs)) ++
      map[List[A],
           List[A]](((aa : List[A]) => b :: aa), listmerge[A](a :: as, bs))
}

def tsmerge[A](x0 : List[List[A]]) : List[List[A]] = x0 match {
  case Nil => List(Nil)
  case List(a) => List(a)
  case a :: b :: ls =>
    maps[List[A],
          List[A]](((merged : List[A]) => tsmerge[A](merged :: ls)),
                    listmerge[A](a, b))
}

def mergetrans[A : countable](ls : List[List[A]]) : List[(Unit,
                   stream[List[A]])]
  =
  map[List[A],
       (Unit,
         stream[List[A]])](((l : List[A]) => ((), sup[List[A]](l))),
                            tsmerge[A](ls))

def mergeaut[A : countable] : listautomaton_ext[Unit, List[List[A]],
         stream[List[A]], Unit]
  =
  listautomaton_exta[Unit, List[List[A]], stream[List[A]],
                      Unit](((_ : Unit) =>
                              ((a : List[List[A]]) => mergetrans[A](a))),
                             List(((), stream_bottom_nc[List[A]]())), ())

def listtransition[A, B, C : conc,
                    D](x0 : listautomaton_ext[A, B, C,
       D]) : A => B => List[(A, C)]
  =
  x0 match {
  case listautomaton_exta(listTransition, listInitConfig, more) =>
    listTransition
}

def listinitconfig[A, B, C : conc,
                    D](x0 : listautomaton_ext[A, B, C, D]) : List[(A, C)]
  =
  x0 match {
  case listautomaton_exta(listTransition, listInitConfig, more) =>
    listInitConfig
}

def of_nat_aux[A : semiring_1](inc : A => A, x1 : nat, i : A) : A = (inc, x1, i)
  match {
  case (inc, zero_nat(), i) => i
  case (inc, Suc(n), i) => of_nat_aux[A](inc, n, inc(i))
}

def of_nat[A : semiring_1](n : nat) : A =
  of_nat_aux[A](((i : A) => plus[A](i, one[A])), n, zero[A])

def integer_of_nat : nat => BigInt = ((a : nat) => of_nat[BigInt](a))

def natural_of_nat(n : nat) : natural =
  natural_of_integer(integer_of_nat.apply(n))

def plus_nat(x0 : nat, n : nat) : nat = (x0, n) match {
  case (Suc(m), n) => plus_nat(m, Suc(n))
  case (zero_nat(), n) => n
}

def one_nat : nat = Suc(zero_nat())

def nat_of_integer(k : BigInt) : nat =
  (k <= BigInt(0) match { case true => zero_nat()
    case false => {
                    val (l, j) =
                      divmod_integer(k, BigInt(2)) : ((BigInt, BigInt))
                    val la = nat_of_integer(l) : nat
                    val lb = plus_nat(la, la) : nat;
                    (j == BigInt(0) match { case true => lb
                      case false => plus_nat(lb, one_nat) })
                  }
    })

def nat_of_natural : natural => nat =
  comp[BigInt, nat,
        natural](((a : BigInt) => nat_of_integer(a)),
                  ((a : natural) => integer_of_natural(a)))

def size_list[A] : (List[A]) => nat =
  ((a : List[A]) => gen_length[A](zero_nat(), a))

def listfun[A](list : List[A], n : natural) : A =
  nth[A](list,
          nat_of_natural.apply(modulo_natural(n,
       natural_of_nat(size_list[A].apply(list)))))

def listtoexec[A, B,
                C : conc](laut : listautomaton_ext[A, B, C,
            Unit]) : execautomaton_ext[A, B, C, Unit]
  =
  execautomaton_exta[A, B, C,
                      Unit](((state : A) => (msg : B) =>
                              ((a : natural) =>
                                listfun[(A,
  C)]((listtransition[A, B, C, Unit](laut)).apply(state).apply(msg), a))),
                             ((a : natural) =>
                               listfun[(A,
 C)](listinitconfig[A, B, C, Unit](laut), a)),
                             ())

def exauttransition[A, B, C : conc,
                     D](x0 : execautomaton_ext[A, B, C,
        D]) : A => B => natural => (A, C)
  =
  x0 match {
  case execautomaton_exta(exautTransition, exautInitConfig, more) =>
    exautTransition
}

def apfst[A, B, C](f : A => B, x1 : (A, C)) : (B, C) = (f, x1) match {
  case (f, (x, y)) => (f(x), y)
}

def rndtransition[A, B,
                   C : conc](eaut : execautomaton_ext[A, B, C, Unit],
                              x1 : (A, (natural, natural)),
                              msg : B) : ((A, (natural, natural)), C)
  =
  (eaut, x1, msg) match {
  case (eaut, (state, seed), msg) =>
    {
      val (nat, nextSeed) = next(seed) : ((natural, (natural, natural)));
      apfst[A, (A, (natural, natural)),
             C](((s : A) => (s, nextSeed)),
                 (exauttransition[A, B, C,
                                   Unit](eaut)).apply(state).apply(msg).apply(nat))
    }
}

def exautinitconfig[A, B, C : conc,
                     D](x0 : execautomaton_ext[A, B, C, D]) : natural => (A, C)
  =
  x0 match {
  case execautomaton_exta(exautTransition, exautInitConfig, more) =>
    exautInitConfig
}

def rndinitconfig[A, B,
                   C : conc](eaut : execautomaton_ext[A, B, C, Unit],
                              seed : (natural,
                                       natural)) : ((A, (natural, natural)), C)
  =
  {
    val (nat, nextSeed) = next(seed) : ((natural, (natural, natural)));
    apfst[A, (A, (natural, natural)),
           C](((s : A) => (s, nextSeed)),
               (exautinitconfig[A, B, C, Unit](eaut)).apply(nat))
  }

def exectoda[A, B,
              C : conc](aut : execautomaton_ext[A, B, C, Unit],
                         seed : (natural,
                                  natural)) : dautomaton_ext[(A,
                       (natural, natural)),
                      B, C, Unit]
  =
  dautomaton_exta[(A, (natural, natural)), B, C,
                   Unit](((a : (A, (natural, natural))) => (b : B) =>
                           rndtransition[A, B, C](aut, a, b)),
                          rndinitconfig[A, B, C](aut, seed), ())

def execmergesem_nc[A : countable : equal](seed : (natural, natural),
    s : stream[List[List[A]]]) : stream[List[A]]
  =
  execsem_nc[(Unit, (natural, natural)), List[List[A]],
              stream[List[A]]](exectoda[Unit, List[List[A]],
 stream[List[A]]](listtoexec[Unit, List[List[A]], stream[List[A]]](mergeaut[A]),
                   seed),
                                s)

def tstimedtoorigin[A : one_chan](x0 : tstimed[A]) : A = x0 match {
  case TSTIMEDA(cs) => cs
}

def slisttoevent_nc[A : countable](x0 : stream[List[A]]) : stream[event[A]] = x0
  match {
  case lscons_u_nc(x :: xs, s) =>
    sconc_nc[event[A]](sup[event[A]](Eventmsg[A](x)),
                        slisttoevent_nc[A](sconc_nc[List[A]](sup[List[A]](xs),
                      s)))
  case lscons_u_nc(Nil, s) =>
    sconc_nc[event[A]](sup[event[A]](Tick[A]()), slisttoevent_nc[A](s))
  case stream_bottom_nc() => stream_bottom_nc[event[A]]()
}

def sdrop_nc[A : countable](n : nat, s : stream[A]) : stream[A] = (n, s) match {
  case (n, stream_bottom_nc()) => stream_bottom_nc[A]()
  case (zero_nat(), s) => s
  case (Suc(n), lscons_u_nc(a, b)) => sdrop_nc[A](n, b)
}

def sbdrop_nc[A : chan](a : nat, b : sb[A]) : sb[A] =
  Abs_lsb[A](((c : A) => sdrop_nc[M](a, (Rep_lsb[A](b)).apply(c))))

def tsexecstatesem_nc[A, B : chan : enuma : equal,
                       C : bot_nc : conc](aut : dautomaton_ext[A, sbelem[B], C,
                        Unit],
   s : A) : (sb[B]) => C
  =
  ((sb : sb[B]) =>
    (! (sbhdelemwell[B](sb)) &&
       ! (equal_set[channel](chandom[B](DUMMY[B]()), bot_set[channel])) match {
      case true => bot_nc[C]
      case false => (Rep_cfun[C, C](conc[C](snd[A,
         C]((dauttransition[A, sbelem[B], C,
                             Unit](aut)).apply(s).apply(sbhdelem[B](sb))))))(implicitly[bot_nc[C]],
                                      implicitly[bot_nc[C]]).apply((tsexecstatesem_nc[A,
       B, C](aut, fst[A, C]((dauttransition[A, sbelem[B], C,
     Unit](aut)).apply(s).apply(sbhdelem[B](sb))))).apply(sbdrop_nc[B](one_nat,
                                sb)))
      }))

def tsexecsem[C, A : chan : enuma : equal,
               B : bot_nc : conc](aut : dautomaton_ext[C, sbelem[A], B,
                Unit]) : cfun[sb[A], B]
  =
  Abs_cfun[sb[A],
            B](((sb : sb[A]) =>
                 (Rep_cfun[B, B](conc[B](snd[C,
      B](dautinitconfig[C, sbelem[A], B,
                         Unit](aut)))))(implicitly[bot_nc[B]],
 implicitly[bot_nc[B]]).apply((tsexecstatesem_nc[C, A,
          B](aut, fst[C, B](dautinitconfig[C, sbelem[A], B,
    Unit](aut)))).apply(sb))))

def thea[A](x0 : Option[A]) : A = x0 match {
  case Some(x2) => x2
}

def sbelist[A : chan](c : A, sbe : sbelem[A]) : List[msg] =
  m2list((member[channel](Rep[A](c), chandom[A](DUMMY[A]())) match {
           case true => (thea[A => M](Rep_sbelem[A](sbe))).apply(c)
           case false => sys.error("undefined") }))

def convtrans[A : tschan : enuma](sbe : sbelem[A]) : List[List[(A, msg)]] =
  (equal_set[channel](chandom[A](DUMMY[A]()), bot_set[channel]) match {
    case true => Nil
    case false => map[A, List[(A, msg)]](((c : A) =>
   map[msg, (A, msg)](((a : msg) => (c, a)), sbelist[A](c, sbe))),
  enuma[A])
    })

def convertaut[A : tschan : enuma] : dautomaton_ext[Unit, sbelem[A],
             stream[List[List[(A, msg)]]], Unit]
  =
  dautomaton_exta[Unit, sbelem[A], stream[List[List[(A, msg)]]],
                   Unit](((_ : Unit) => (sb : sbelem[A]) =>
                           ((), sup[List[List[(A, msg)]]](convtrans[A](sb)))),
                          ((), stream_bottom_nc[List[List[(A, msg)]]]()), ())

def convertsem[A : tschan : enuma : equal] : cfun[sb[A],
           stream[List[List[(A, msg)]]]]
  =
  tsexecsem[Unit, A, stream[List[List[(A, msg)]]]](convertaut[A])

def sscanla_nc[A, B : countable,
                C : bot_nc : conc](f : A => B => (A, C), s : A,
                                    x2 : stream[B]) : C
  =
  (f, s, x2) match {
  case (f, s, lscons_u_nc(a, b)) =>
    (Rep_cfun[C, C](conc[C](snd[A, C]((f(s))(a)))))(implicitly[bot_nc[C]],
             implicitly[bot_nc[C]]).apply(sscanla_nc[A, B,
              C](f, fst[A, C]((f(s))(a)), b))
  case (x, xa, stream_bottom_nc()) => bot_nc[C]
}

def tolisthelper[A : countable](s : List[A],
                                 x1 : event[A]) : (List[A], stream[List[A]])
  =
  (s, x1) match {
  case (s, Tick()) => (Nil, sup[List[A]](s))
  case (s, Eventmsg(m)) => (s ++ List(m), stream_bottom_nc[List[A]]())
}

def seventtolist_nc[A : countable : equal](s : stream[event[A]]) : stream[List[A]]
  =
  sscanla_nc[List[A], event[A],
              stream[List[A]]](((a : List[A]) => (b : event[A]) =>
                                 tolisthelper[A](a, b)),
                                Nil, s)

def m2event(x0 : M) : event[msg] = x0 match {
  case Timed(Tlive(e)) => e
  case Timed(Tfin(Nil)) => Tick[msg]()
  case Timed(Tfin(x :: xs)) => Eventmsg[msg](x)
  case Untimed(e) => Eventmsg[msg](e)
  case Timed(Tsyna(Eps())) => Tick[msg]()
  case Timed(Tsyna(Tsynmsg(v))) => sys.error("undefined")
  case Timed(Tonea(va)) => Eventmsg[msg](va)
}

def sbgetch_nc[A : chan, B : chan](c : A, sb : sb[B]) : stream[M] =
  (member[channel](Rep[A](c), chandom[B](DUMMY[B]())) match {
    case true => (Rep_lsb[B](sb)).apply(Abs[B](Rep[A](c)))
    case false => stream_bottom_nc[M]() })

def inconv_nc[A : echan : enuma](sb : sb[A]) : sb[tstimed[A]] =
  Abs_lsb[tstimed[A]](((c : tstimed[A]) =>
                        smap_nc[List[msg],
                                 M](comp[M_timed, M,
  List[msg]](((a : M_timed) => Timed(a)), ((a : List[msg]) => Tfin(a))),
                                     seventtolist_nc[msg](smap_nc[M,
                           event[msg]](((a : M) => m2event(a)),
sbgetch_nc[A, A](tstimedtoorigin[A](c), sb))))))

def execbmerge[A : echan : enuma : equal](seed : (natural, natural),
   sb : sb[A]) : eventwellstream[A]
  =
  Abs_eventwellstream[A](emap_nc[(tstimed[A], msg),
                                  (A, msg)](((a : (tstimed[A], msg)) =>
      {
        val (c, aa) = a : ((tstimed[A], msg));
        (tstimedtoorigin[A](c), aa)
      }),
     slisttoevent_nc[(tstimed[A],
                       msg)](execmergesem_nc[(tstimed[A],
       msg)](seed,
              (Rep_cfun[sb[tstimed[A]],
                         stream[List[List[(tstimed[A],
    msg)]]]](convertsem[tstimed[A]])).apply(inconv_nc[A](sb))))))

def execsem(x0 : (Unit, ((natural, natural), (natural, natural))),
             sb : sb[channels]) : sb[channelsa]
  =
  (x0, sb) match {
  case ((p, (seed1, seed2)), sb) =>
    execsem_nc[(State, (natural, natural)), event[(channels, msg)],
                sb[channelsa]](exectoda[State, event[(channels, msg)],
 sb[channelsa]](listtoexec[State, event[(channels, msg)],
                            sb[channelsa]](laut(p)),
                 seed1),
                                Rep_eventwellstream[channels](execbmerge[channels](seed2,
    sb)))
}

def channelschan[A, B](boolEVENTConv : A => B, beInChannel_pattern : A,
                        x2 : channels) : B
  =
  (boolEVENTConv, beInChannel_pattern, x2) match {
  case (boolEVENTConv, beInChannel_pattern, beinchannel_rep()) =>
    boolEVENTConv(beInChannel_pattern)
}

def buildsb : (stream[event[Boolean]]) => channels => stream[M] =
  ((a : stream[event[Boolean]]) => (b : channels) =>
    channelschan[stream[event[Boolean]],
                  stream[M]](((aa : stream[event[Boolean]]) =>
                               smap_nc[event[Boolean],
M](comp[event[msg], M,
         event[Boolean]](comp[M_timed, M,
                               event[msg]](((ab : M_timed) => Timed(ab)),
    ((ab : event[msg]) => Tlive(ab))),
                          ((ab : event[Boolean]) =>
                            map_event[Boolean,
                                       msg](((ac : Boolean) =>
      booleventconstr(ac)),
     ab))),
    aa)),
                              a, b))

def insbsetter_nc(a : stream[event[Boolean]]) : sb[channels] =
  Abs_lsb[channels](buildsb.apply(a))

def sbsetter : cfun[stream[event[Boolean]], sb[channels]] =
  Abs_cfun[stream[event[Boolean]],
            sb[channels]](((a : stream[event[Boolean]]) => insbsetter_nc(a)))

def conv_bool(x0 : M) : event[Boolean] = x0 match {
  case Timed(Tlive(Eventmsg(booleventconstr(a)))) => Eventmsg[Boolean](a)
  case Timed(Tlive(Tick())) => Tick[Boolean]()
  case Untimed(va) => conv_bool(Untimed(va))
  case Timed(Tsyna(vb)) => conv_bool(Timed(Tsyna(vb)))
  case Timed(Tonea(vb)) => conv_bool(Timed(Tonea(vb)))
  case Timed(Tlive(Eventmsg(boolsyncconstr(vd)))) =>
    conv_bool(Timed(Tlive(Eventmsg[msg](boolsyncconstr(vd)))))
  case Timed(Tlive(Eventmsg(nateventconstr(vd)))) =>
    conv_bool(Timed(Tlive(Eventmsg[msg](nateventconstr(vd)))))
  case Timed(Tlive(Eventmsg(natsyncconstr(vd)))) =>
    conv_bool(Timed(Tlive(Eventmsg[msg](natsyncconstr(vd)))))
  case Timed(Tlive(Eventmsg(stringeventconstr(vd)))) =>
    conv_bool(Timed(Tlive(Eventmsg[msg](stringeventconstr(vd)))))
  case Timed(Tlive(Eventmsg(stringsyncconstr(vd)))) =>
    conv_bool(Timed(Tlive(Eventmsg[msg](stringsyncconstr(vd)))))
  case Timed(Tfin(vb)) => conv_bool(Timed(Tfin(vb)))
}

def conv_boola(x0 : M) : event[Boolean] = x0 match {
  case Timed(Tlive(Eventmsg(booleventconstr(a)))) => Eventmsg[Boolean](a)
  case Timed(Tlive(Tick())) => Tick[Boolean]()
  case Untimed(va) => conv_bool(Untimed(va))
  case Timed(Tsyna(vb)) => conv_bool(Timed(Tsyna(vb)))
  case Timed(Tonea(vb)) => conv_bool(Timed(Tonea(vb)))
  case Timed(Tlive(Eventmsg(boolsyncconstr(vd)))) =>
    conv_bool(Timed(Tlive(Eventmsg[msg](boolsyncconstr(vd)))))
  case Timed(Tlive(Eventmsg(nateventconstr(vd)))) =>
    conv_bool(Timed(Tlive(Eventmsg[msg](nateventconstr(vd)))))
  case Timed(Tlive(Eventmsg(natsyncconstr(vd)))) =>
    conv_bool(Timed(Tlive(Eventmsg[msg](natsyncconstr(vd)))))
  case Timed(Tlive(Eventmsg(stringeventconstr(vd)))) =>
    conv_bool(Timed(Tlive(Eventmsg[msg](stringeventconstr(vd)))))
  case Timed(Tlive(Eventmsg(stringsyncconstr(vd)))) =>
    conv_bool(Timed(Tlive(Eventmsg[msg](stringsyncconstr(vd)))))
  case Timed(Tfin(vb)) => conv_bool(Timed(Tfin(vb)))
}

def sbgetter : cfun[sb[channelsa], stream[event[Boolean]]] =
  Abs_cfun[sb[channelsa],
            stream[event[Boolean]]](((a : sb[channelsa]) =>
                                      smap_nc[M,
       event[Boolean]](((aa : M) => conv_boola(aa)),
                        (Rep_lsb[channelsa](a)).apply(beoutchannel_rep()))))

def sb2stream(a : sb[channelsa]) : stream[event[Boolean]] =
  (Rep_cfun[sb[channelsa], stream[event[Boolean]]](sbgetter)).apply(a)

}
