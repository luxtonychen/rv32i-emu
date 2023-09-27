module HwSignal

import BitsVec
import public Event

public export
RegIdx : Type
RegIdx = Event (BitsVec 5)

public export
Dat : Type
Dat = Event (BitsVec 32)
