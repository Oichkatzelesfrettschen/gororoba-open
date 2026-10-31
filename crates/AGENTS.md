# Crate conventions

## GPU helper crates

| Crate (feature) | Owns |
| --- | --- |
| `gororoba_gpu_bridge` | `ComputeBackend`, `HardwareCaps`, `StoragePrecision` vocabulary |
| `gororoba_gpu_vulkan` (`ash`) | `InstanceBuilder`, `Adapter::pick`, `DeviceBuilder`, `ShaderModule::from_wgsl`, `DescriptorSetLayoutSpec`, `ComputePipelineBuilder`, `DispatchScope` |
| `gororoba_gpu_cubecl` (`cubecl`) | `Runtime::probe`, `test_support::skip_if_unavailable!` |
| `gororoba_gpu_cuda` (`cudarc`) | `Context::with_default_device`, `DeviceProbe::query`, `CompileOptions::for_arch`, `ModuleRegistry::load`, `Buffer<T>`, `ManagedBuffer<T>`, `LaunchConfig::launch_1d/2d/3d`, `telemetry::Telemetry`, `optix::PipelineBuilder` |

All helper crates ship empty `default` features. New code MUST route Vulkan,
cubecl-wgpu and CUDA setup through them rather than calling `Entry::load`,
`CudaContext::new(0)` or NVRTC options directly.

## Generated code

`data_core/src/registry_mirrors/` is generated from the registry; regenerate
through the export in `registry/AGENTS.md`.
