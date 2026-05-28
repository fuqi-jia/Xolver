"""eval._compat — Python 3.6 safety shim.

panda14 runs Python 3.6, where stdlib `dataclasses` (3.7+) is absent. eval's
data holders are plain (annotated fields, simple defaults, one default_factory),
so a minimal fallback covers them. Uses the real stdlib `dataclass`/`field` when
available; falls back otherwise. Set EVAL_FORCE_DATACLASS_FALLBACK=1 to force the
fallback on 3.7+ (used by the test suite to validate the 3.6 path).

Python 3.6+ / stdlib only.
"""
import os


class _Missing:
    pass


MISSING = _Missing()


class _Field:
    __slots__ = ("default", "default_factory")

    def __init__(self, default=MISSING, default_factory=MISSING):
        self.default = default
        self.default_factory = default_factory


def fallback_field(default=MISSING, default_factory=MISSING):
    return _Field(default, default_factory)


def fallback_dataclass(cls):
    """Minimal @dataclass: generates __init__/__repr__/__eq__ from annotations.

    Supports class-level simple defaults and field(default_factory=...). No
    inheritance / frozen / __post_init__ (eval needs none). Field order follows
    __annotations__ (definition order on CPython 3.6+).
    """
    annotations = getattr(cls, "__annotations__", {})
    fields = []  # (name, default, default_factory)
    for name in annotations:
        if name in cls.__dict__:
            val = cls.__dict__[name]
            if isinstance(val, _Field):
                fields.append((name, val.default, val.default_factory))
            else:
                fields.append((name, val, MISSING))
        else:
            fields.append((name, MISSING, MISSING))

    def __init__(self, *args, **kwargs):
        if len(args) > len(fields):
            raise TypeError("%s() takes at most %d positional arguments (%d given)"
                            % (cls.__name__, len(fields), len(args)))
        seen = set()
        for i, a in enumerate(args):
            setattr(self, fields[i][0], a)
            seen.add(fields[i][0])
        for name, default, dfac in fields:
            if name in seen:
                continue
            if name in kwargs:
                setattr(self, name, kwargs.pop(name))
            elif dfac is not MISSING:
                setattr(self, name, dfac())
            elif default is not MISSING:
                setattr(self, name, default)
            else:
                raise TypeError("%s() missing required argument: %r" % (cls.__name__, name))
        if kwargs:
            raise TypeError("%s() got unexpected keyword arguments %s"
                            % (cls.__name__, sorted(kwargs)))

    def __repr__(self):
        return cls.__name__ + "(" + ", ".join(
            "%s=%r" % (n, getattr(self, n)) for n, _, _ in fields) + ")"

    def __eq__(self, other):
        if other.__class__ is not self.__class__:
            return NotImplemented
        return tuple(getattr(self, n) for n, _, _ in fields) == \
            tuple(getattr(other, n) for n, _, _ in fields)

    cls.__init__ = __init__
    cls.__repr__ = __repr__
    cls.__eq__ = __eq__
    # Drop _Field sentinels left as class attributes so they don't leak as values.
    for name, _, _ in fields:
        if isinstance(cls.__dict__.get(name), _Field):
            delattr(cls, name)
    return cls


if os.environ.get("EVAL_FORCE_DATACLASS_FALLBACK") == "1":
    dataclass = fallback_dataclass
    field = fallback_field
else:
    try:
        from dataclasses import dataclass, field  # noqa: F401  (Python 3.7+)
    except ImportError:  # Python 3.6 without the dataclasses backport
        dataclass = fallback_dataclass
        field = fallback_field
