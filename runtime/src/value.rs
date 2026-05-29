use crate::ids::ActorId;
use std::sync::Arc as StdArc;

#[derive(Debug, Clone)]
pub struct MorphString {
    data: StdArc<str>,
}

impl MorphString {
    pub fn new(s: &str) -> Self {
        MorphString { data: s.into() }
    }

    pub fn as_str(&self) -> &str {
        &self.data
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }
}

impl std::fmt::Display for MorphString {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.data)
    }
}

impl PartialEq for MorphString {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
    }
}

impl std::borrow::Borrow<str> for MorphString {
    fn borrow(&self) -> &str {
        &self.data
    }
}

#[derive(Debug, Clone)]
pub struct MorphStruct {
    pub type_name: String,
    pub fields: Vec<(String, MorphValue)>,
}

impl MorphStruct {
    pub fn new(type_name: &str, fields: Vec<(String, MorphValue)>) -> Self {
        MorphStruct {
            type_name: type_name.to_string(),
            fields,
        }
    }

    pub fn get_field(&self, name: &str) -> Option<&MorphValue> {
        self.fields.iter().find(|(n, _)| n == name).map(|(_, v)| v)
    }
}

#[derive(Debug, Clone)]
pub struct MorphEnum {
    pub type_name: String,
    pub variant: String,
    pub payload: Option<Box<MorphValue>>,
}

impl MorphEnum {
    pub fn new(type_name: &str, variant: &str, payload: Option<MorphValue>) -> Self {
        MorphEnum {
            type_name: type_name.to_string(),
            variant: variant.to_string(),
            payload: payload.map(Box::new),
        }
    }
}

#[derive(Debug, Clone)]
pub struct FunctionRef {
    pub id: u64,
    pub name: String,
}

impl FunctionRef {
    pub fn new(id: u64, name: &str) -> Self {
        FunctionRef {
            id,
            name: name.to_string(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Pointer {
    Raw(u64),
    ArcHandle(u64),
}

#[derive(Debug, Clone, PartialEq)]
pub enum MessagePayload {
    Value(MorphValue),
    Signal(SignalType),
}

#[derive(Debug, Clone, PartialEq)]
pub enum SignalType {
    Poison,
    Terminate,
    Custom(String),
}

#[derive(Debug, Clone)]
pub enum MorphValue {
    Bool(bool),
    Int8(i8),
    Int16(i16),
    Int32(i32),
    Int64(i64),
    UInt8(u8),
    UInt16(u16),
    UInt32(u32),
    UInt64(u64),
    Float32(f32),
    Float64(f64),
    String(MorphString),
    Unit,
    Optional(Option<Box<MorphValue>>),
    Result(Result<Box<MorphValue>, Box<MorphValue>>),
    Struct(MorphStruct),
    Enum(MorphEnum),
    Array(Vec<MorphValue>),
    Tuple(Vec<MorphValue>),
    Function(FunctionRef),
    ActorRef(ActorId),
    Pointer(Pointer),
}

impl MorphValue {
    pub fn type_name(&self) -> &'static str {
        match self {
            MorphValue::Bool(_) => "bool",
            MorphValue::Int8(_) => "i8",
            MorphValue::Int16(_) => "i16",
            MorphValue::Int32(_) => "i32",
            MorphValue::Int64(_) => "i64",
            MorphValue::UInt8(_) => "u8",
            MorphValue::UInt16(_) => "u16",
            MorphValue::UInt32(_) => "u32",
            MorphValue::UInt64(_) => "u64",
            MorphValue::Float32(_) => "f32",
            MorphValue::Float64(_) => "f64",
            MorphValue::String(_) => "str",
            MorphValue::Unit => "void",
            MorphValue::Optional(_) => "optional",
            MorphValue::Result(_) => "result",
            MorphValue::Struct(_) => "struct",
            MorphValue::Enum(_) => "enum",
            MorphValue::Array(_) => "array",
            MorphValue::Tuple(_) => "tuple",
            MorphValue::Function(_) => "function",
            MorphValue::ActorRef(_) => "actor",
            MorphValue::Pointer(_) => "pointer",
        }
    }

    pub fn is_truthy(&self) -> bool {
        match self {
            MorphValue::Bool(b) => *b,
            MorphValue::Int64(n) => *n != 0,
            MorphValue::UInt64(n) => *n != 0,
            MorphValue::Float64(f) => *f != 0.0,
            MorphValue::String(s) => !s.as_str().is_empty(),
            MorphValue::Unit => false,
            MorphValue::Optional(opt) => opt.is_some(),
            MorphValue::Array(arr) => !arr.is_empty(),
            _ => true,
        }
    }

    pub fn as_bool(&self) -> Option<bool> {
        match self {
            MorphValue::Bool(b) => Some(*b),
            _ => None,
        }
    }

    pub fn as_int64(&self) -> Option<i64> {
        match self {
            MorphValue::Int8(v) => Some(*v as i64),
            MorphValue::Int16(v) => Some(*v as i64),
            MorphValue::Int32(v) => Some(*v as i64),
            MorphValue::Int64(v) => Some(*v),
            _ => None,
        }
    }

    pub fn as_float64(&self) -> Option<f64> {
        match self {
            MorphValue::Float32(v) => Some(*v as f64),
            MorphValue::Float64(v) => Some(*v),
            _ => None,
        }
    }
}

impl PartialEq for MorphValue {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (MorphValue::Bool(a), MorphValue::Bool(b)) => a == b,
            (MorphValue::Int8(a), MorphValue::Int8(b)) => a == b,
            (MorphValue::Int16(a), MorphValue::Int16(b)) => a == b,
            (MorphValue::Int32(a), MorphValue::Int32(b)) => a == b,
            (MorphValue::Int64(a), MorphValue::Int64(b)) => a == b,
            (MorphValue::UInt8(a), MorphValue::UInt8(b)) => a == b,
            (MorphValue::UInt16(a), MorphValue::UInt16(b)) => a == b,
            (MorphValue::UInt32(a), MorphValue::UInt32(b)) => a == b,
            (MorphValue::UInt64(a), MorphValue::UInt64(b)) => a == b,
            (MorphValue::Float32(a), MorphValue::Float32(b)) => a == b,
            (MorphValue::Float64(a), MorphValue::Float64(b)) => a == b,
            (MorphValue::String(a), MorphValue::String(b)) => a == b,
            (MorphValue::Unit, MorphValue::Unit) => true,
            (MorphValue::ActorRef(a), MorphValue::ActorRef(b)) => a == b,
            (MorphValue::Pointer(a), MorphValue::Pointer(b)) => a == b,
            (MorphValue::Array(a), MorphValue::Array(b)) => a == b,
            (MorphValue::Tuple(a), MorphValue::Tuple(b)) => a == b,
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_value_type_names() {
        assert_eq!(MorphValue::Bool(true).type_name(), "bool");
        assert_eq!(MorphValue::Int32(42).type_name(), "i32");
        assert_eq!(MorphValue::Float64(3.15).type_name(), "f64");
        assert_eq!(MorphValue::Unit.type_name(), "void");
        assert_eq!(
            MorphValue::String(MorphString::new("hi")).type_name(),
            "str"
        );
        assert_eq!(MorphValue::Array(vec![]).type_name(), "array");
    }

    #[test]
    fn test_value_truthiness() {
        assert!(MorphValue::Bool(true).is_truthy());
        assert!(!MorphValue::Bool(false).is_truthy());
        assert!(!MorphValue::Int64(0).is_truthy());
        assert!(MorphValue::Int64(1).is_truthy());
        assert!(!MorphValue::Unit.is_truthy());
        assert!(!MorphValue::String(MorphString::new("")).is_truthy());
        assert!(MorphValue::String(MorphString::new("x")).is_truthy());
    }

    #[test]
    fn test_value_equality() {
        assert_eq!(MorphValue::Int32(42), MorphValue::Int32(42));
        assert_ne!(MorphValue::Int32(42), MorphValue::Int64(42));
        assert_eq!(
            MorphValue::Array(vec![MorphValue::Int32(1), MorphValue::Int32(2)]),
            MorphValue::Array(vec![MorphValue::Int32(1), MorphValue::Int32(2)])
        );
    }

    #[test]
    fn test_struct_field_access() {
        let s = MorphStruct::new(
            "Point",
            vec![
                ("x".to_string(), MorphValue::Float64(1.0)),
                ("y".to_string(), MorphValue::Float64(2.0)),
            ],
        );
        assert_eq!(s.get_field("x").unwrap().as_float64(), Some(1.0));
        assert_eq!(s.get_field("y").unwrap().as_float64(), Some(2.0));
        assert!(s.get_field("z").is_none());
    }
}
