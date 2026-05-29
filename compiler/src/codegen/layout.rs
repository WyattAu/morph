use std::collections::HashMap;

use crate::typeck::types::{FloatKind, IntKind, Ty};

use super::morph_ir::{FieldInfo, TypeInfo, TypeInfoKind, VariantInfo};

#[derive(Debug, Clone)]
pub struct TypeLayout {
    pub size: u32,
    pub alignment: u32,
}

impl TypeLayout {
    pub fn new(size: u32, alignment: u32) -> Self {
        Self { size, alignment }
    }
}

#[derive(Debug, Clone, Default)]
pub struct TypeRegistry {
    structs: HashMap<String, Vec<(String, Ty)>>,
    enums: HashMap<String, Vec<(String, Vec<Ty>)>>,
}

impl TypeRegistry {
    pub fn new() -> Self {
        Self {
            structs: HashMap::new(),
            enums: HashMap::new(),
        }
    }

    pub fn register_struct(&mut self, name: String, fields: Vec<(String, Ty)>) {
        self.structs.insert(name, fields);
    }

    pub fn register_enum(&mut self, name: String, variants: Vec<(String, Vec<Ty>)>) {
        self.enums.insert(name, variants);
    }

    pub fn lookup_struct(&self, name: &str) -> Option<&Vec<(String, Ty)>> {
        self.structs.get(name)
    }

    pub fn lookup_enum(&self, name: &str) -> Option<&Vec<(String, Vec<Ty>)>> {
        self.enums.get(name)
    }
}

pub fn compute_layout(ty: &Ty, registry: &TypeRegistry) -> TypeLayout {
    match ty {
        Ty::Bool => TypeLayout::new(1, 1),
        Ty::Int(kind) => {
            let (size, align) = int_layout(*kind);
            TypeLayout::new(size, align)
        }
        Ty::Float(kind) => {
            let (size, align) = float_layout(*kind);
            TypeLayout::new(size, align)
        }
        Ty::Str => TypeLayout::new(8, 8), // pointer-sized
        Ty::Void => TypeLayout::new(0, 1),
        Ty::Never => TypeLayout::new(0, 1),
        Ty::Tuple(elements) => {
            if elements.is_empty() {
                return TypeLayout::new(0, 1);
            }
            let layouts: Vec<TypeLayout> = elements
                .iter()
                .map(|e| compute_layout(e, registry))
                .collect();
            tuple_layout(&layouts)
        }
        Ty::Array(inner) => {
            let element = compute_layout(inner, registry);
            let size = element.size * 1; // single element base; real array needs count
            let align = element.alignment;
            TypeLayout::new(size.max(align), align)
        }
        Ty::Optional(inner) => {
            let inner_layout = compute_layout(inner, registry);
            let tag_size = 1u32;
            let align = inner_layout.alignment.max(1);
            let padded_inner = align_to(inner_layout.size, align);
            TypeLayout::new(tag_size + padded_inner, align)
        }
        Ty::Result { ok, err } => {
            let ok_layout = compute_layout(ok, registry);
            let err_layout = compute_layout(err, registry);
            let payload_size = ok_layout.size.max(err_layout.size);
            let tag_size = 1u32;
            let align = ok_layout.alignment.max(err_layout.alignment).max(1);
            let padded_payload = align_to(payload_size, align);
            TypeLayout::new(tag_size + padded_payload, align)
        }
        Ty::Named { name, args: _ } => {
            if let Some(fields) = registry.lookup_struct(name) {
                let (size, align, _) = compute_struct_layout(fields, registry);
                return TypeLayout::new(size, align);
            }
            if let Some(variants) = registry.lookup_enum(name) {
                let (size, align, _) = compute_enum_layout_from_types(variants, registry);
                return TypeLayout::new(size, align);
            }
            TypeLayout::new(0, 1)
        }
        Ty::Ref { .. } => TypeLayout::new(8, 8), // pointer-sized
        Ty::Fn { .. } => TypeLayout::new(8, 8),  // function pointer
        Ty::Actor(_) => TypeLayout::new(8, 8),    // actor reference
        Ty::TypeVar(_) => TypeLayout::new(8, 8),
        Ty::Error => TypeLayout::new(0, 1),
    }
}

fn int_layout(kind: IntKind) -> (u32, u32) {
    match kind {
        IntKind::I8 | IntKind::U8 => (1, 1),
        IntKind::I16 | IntKind::U16 => (2, 2),
        IntKind::I32 | IntKind::U32 => (4, 4),
        IntKind::I64 | IntKind::U64 => (8, 8),
        IntKind::ISize | IntKind::USize => (8, 8),
    }
}

fn float_layout(kind: FloatKind) -> (u32, u32) {
    match kind {
        FloatKind::F32 => (4, 4),
        FloatKind::F64 => (8, 8),
    }
}

fn align_to(offset: u32, alignment: u32) -> u32 {
    if alignment == 0 {
        return offset;
    }
    let mask = alignment - 1;
    (offset + mask) & !mask
}

fn tuple_layout(layouts: &[TypeLayout]) -> TypeLayout {
    let mut offset: u32 = 0;
    let mut max_align: u32 = 1;
    for layout in layouts {
        max_align = max_align.max(layout.alignment);
        offset = align_to(offset, layout.alignment);
        offset += layout.size;
    }
    offset = align_to(offset, max_align);
    TypeLayout::new(offset, max_align)
}

pub fn compute_struct_layout(
    fields: &[(String, Ty)],
    registry: &TypeRegistry,
) -> (u32, u32, Vec<FieldInfo>) {
    let mut offset: u32 = 0;
    let mut max_align: u32 = 1;
    let mut field_infos = Vec::with_capacity(fields.len());

    for (name, ty) in fields {
        let layout = compute_layout(ty, registry);
        max_align = max_align.max(layout.alignment);
        offset = align_to(offset, layout.alignment);
        field_infos.push(FieldInfo {
            name: name.clone(),
            offset,
            ty: ty.clone(),
        });
        offset += layout.size;
    }

    offset = align_to(offset, max_align);
    (offset, max_align, field_infos)
}

pub fn compute_enum_layout_from_types(
    variants: &[(String, Vec<Ty>)],
    registry: &TypeRegistry,
) -> (u32, u32, Vec<VariantInfo>) {
    let discriminant_size: u32 = 1;
    let discriminant_align: u32 = 1;
    let mut max_payload_size: u32 = 0;
    let mut max_align: u32 = discriminant_align;
    let mut variant_infos = Vec::with_capacity(variants.len());

    for (idx, (name, fields)) in variants.iter().enumerate() {
        let tag = idx as u8;
        let mut variant_size: u32 = 0;
        let mut variant_align: u32 = 1;

        for field_ty in fields {
            let layout = compute_layout(field_ty, registry);
            variant_align = variant_align.max(layout.alignment);
            variant_size = align_to(variant_size, layout.alignment);
            variant_size += layout.size;
        }

        variant_size = align_to(variant_size, variant_align);
        max_payload_size = max_payload_size.max(variant_size);
        max_align = max_align.max(variant_align);

        variant_infos.push(VariantInfo {
            name: name.clone(),
            tag,
            size: variant_size,
            fields: fields.clone(),
        });
    }

    let payload_aligned = align_to(max_payload_size, max_align);
    let total = align_to(discriminant_size + payload_aligned, max_align);

    (total, max_align, variant_infos)
}

pub fn build_type_info(name: &str, ty: &Ty, registry: &TypeRegistry) -> Option<TypeInfo> {
    match ty {
        Ty::Bool | Ty::Int(_) | Ty::Float(_) | Ty::Str => {
            let layout = compute_layout(ty, registry);
            Some(TypeInfo {
                name: name.to_string(),
                size: layout.size,
                alignment: layout.alignment,
                kind: TypeInfoKind::Primitive,
            })
        }
        Ty::Named { name: type_name, .. } => {
            if let Some(fields) = registry.lookup_struct(type_name) {
                let (size, align, field_infos) = compute_struct_layout(fields, registry);
                Some(TypeInfo {
                    name: name.to_string(),
                    size,
                    alignment: align,
                    kind: TypeInfoKind::Struct { fields: field_infos },
                })
            } else if let Some(variants) = registry.lookup_enum(type_name) {
                let (size, align, variant_infos) =
                    compute_enum_layout_from_types(variants, registry);
                Some(TypeInfo {
                    name: name.to_string(),
                    size,
                    alignment: align,
                    kind: TypeInfoKind::Enum {
                        variants: variant_infos,
                    },
                })
            } else {
                None
            }
        }
        _ => None,
    }
}
