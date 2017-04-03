using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using System.Reflection.Emit;
using System.Runtime.Remoting;
using System.Text;
using System.Threading.Tasks;

namespace Kafka
{
    public class CastException : Exception { }
    public class Runtime
    {
        private static AssemblyName classGenName;
        private static AssemblyBuilder ab;
        private static ModuleBuilder mb;
        private static Type runtimeType;
        private static MethodInfo dyWrapperf, tyWrapperf;
        
        static Runtime()
        {
            classGenName = new AssemblyName("CastAssembly");
            ab = AppDomain.CurrentDomain.DefineDynamicAssembly(classGenName, AssemblyBuilderAccess.Run);
            mb = ab.DefineDynamicModule("KafkaWrappers"); //, "KafkaWrapper.dll"
            runtimeType = typeof(Runtime);
            dyWrapperf = runtimeType.GetMethod("dyWrapper");
            tyWrapperf = runtimeType.GetMethod("tyWrapper");
        }

        public static dynamic dyWrapper<T>(T src)
        {
            Type source = typeof(T);
            BindingFlags flags = BindingFlags.Instance | BindingFlags.Public | BindingFlags.DeclaredOnly;

            Dictionary<string, PropertyInfo> srcPropMap;
            Dictionary<string, MethodInfo> srcMethMap;
            MakeMemberMaps(source, flags, out srcPropMap, out srcMethMap);

            // no correctness criteria.
            // emit crank.

            TypeBuilder tb = mb.DefineType(source.Name + "toDynwrapper", TypeAttributes.Public);
            // no interface implementations
            
            var thatf = tb.DefineField("that", source, FieldAttributes.Private);
            MakeConstructor(source, tb, thatf);

            foreach (string k in srcPropMap.Keys)
            {
                MakePropertyWrapper(tb, thatf, k, typeof(object), srcPropMap[k]);
            }

            foreach (string k in srcMethMap.Keys)
            {
                MethodInfo srcInfo = srcMethMap[k];
                MakeMethodWrapper(tb, thatf, k, srcInfo, new Type[] { typeof(object) }, typeof(object), null);
            }

            Type wrapper = tb.CreateType();
            //ab.Save("KafkaWrapper.dll");
            return (dynamic)wrapper.GetConstructor(new Type[] { source }).Invoke(new object[] { src });
        }

        public static T tyWrapper<T>(dynamic src)
        {
            Type source = src.GetType();
            Type target = typeof(T);
            BindingFlags flags = BindingFlags.Instance | BindingFlags.Public | BindingFlags.DeclaredOnly;

            SubtypeOf sts = (SubtypeOf)Attribute.GetCustomAttribute(target, typeof(SubtypeOf));
            Type[] explicitSts = null;
            if (sts == null)
            {
                explicitSts = sts.Subtypes;
            } else
            {
                explicitSts = Type.EmptyTypes;
            }

            Dictionary<string, PropertyInfo> srcPropMap, tgtPropMap;
            Dictionary<string, MethodInfo> srcMethMap, tgtMethMap;
            MakeMemberMaps(source, flags, out srcPropMap, out srcMethMap);
            MakeMemberMaps(target, flags, out tgtPropMap, out tgtMethMap);

            foreach (string k in tgtPropMap.Keys)
            {
                if (!srcPropMap.ContainsKey(k)) throw new CastException();
                if (tgtPropMap[k].CanRead && !srcPropMap[k].CanRead) throw new CastException();
                if (tgtPropMap[k].CanWrite && !srcPropMap[k].CanWrite) throw new CastException();
            }

            foreach (string k in tgtMethMap.Keys)
            {
                if (!srcMethMap.ContainsKey(k)) throw new CastException();
            }

            //all compatibility checks done
            //time to turn the emit crank
            TypeBuilder tb = mb.DefineType(source.Name + "to" + target.Name + "wrapper", TypeAttributes.Public);
            tb.AddInterfaceImplementation(target);
            var thatf = tb.DefineField("that", source, FieldAttributes.Private);
            MakeConstructor(source, tb, thatf);

            foreach (string k in srcPropMap.Keys)
            {
                PropertyInfo tgtProp = null;
                if (tgtPropMap.ContainsKey(k))
                {
                    tgtProp = tgtPropMap[k];
                }
                PropertyInfo srcProp = srcPropMap[k];
                MakePropertyWrapper(tb, thatf, k, tgtProp.PropertyType, srcProp);
            }
            
            foreach (string k in srcMethMap.Keys)
            {
                MethodInfo srcInfo = srcMethMap[k];
                if (tgtMethMap.ContainsKey(k))
                {
                    MethodInfo tgtInfo = tgtMethMap[k];
                    MakeMethodWrapper(tb, thatf, k, srcInfo,
                                             tgtInfo.GetParameters().Select(param => param.ParameterType).ToArray(),
                                             tgtInfo.ReturnType, tgtInfo);
                }
                else
                {
                    MakeMethodWrapper(tb, thatf, k, srcInfo,
                                             srcInfo.GetParameters().Select(param => param.ParameterType).ToArray(),
                                             srcInfo.ReturnType, null);
                }
            }

            foreach (Type mbSt in explicitSts)
            {
                MakeExplicitImplementation(tb, mbSt, flags);
            }

            Type wrapper = tb.CreateType();
            //ab.Save("KafkaWrapper.dll");
            return (T)wrapper.GetConstructor(new Type[] { source }).Invoke(new object[] { src });
        }

        private static void MakeExplicitImplementation(TypeBuilder tb, Type mbSt, BindingFlags bf)
        {
            //We can assume: 
            // * The arguments are actually always going to be subtypes
            // * The return type is going to be statically known to be a subtype
            // * The real function is also on the same class, of the same name
            // If any of these were violated, the original structural rule wouldn't have worked.
            foreach (PropertyInfo pi in mbSt.GetProperties())
            {

            }
            foreach (MethodInfo mi in mbSt.GetMethods(bf))
            {
                var mb = tb.DefineMethod(mi.Name, MethodAttributes.Private | MethodAttributes.HideBySig 
                                                | MethodAttributes.Virtual | MethodAttributes.Final);
                var ilg = mb.GetILGenerator();
                ilg.Emit(OpCodes.Ldarg_0);
                ilg.Emit(OpCodes.Ldarg_1); // always 1 argument.
                //ilg.Emit(OpCodes.Call, )
            }
            throw new NotImplementedException();
        }

        private static void MakeMemberMaps(Type source, BindingFlags flags, out Dictionary<string, PropertyInfo> srcPropMap, out Dictionary<string, MethodInfo> srcMethMap)
        {
            PropertyInfo[] srcProps = source.GetProperties();
            MethodInfo[] srcMeths = source.GetMethods(flags);
            srcPropMap = srcProps.ToDictionary(val => val.Name, val => val);
            srcMethMap = srcMeths.ToDictionary(val => val.Name, val => val);
        }

        private static void MakeConstructor(Type source, TypeBuilder tb, FieldBuilder thatf)
        {
            var cb = tb.DefineConstructor(MethodAttributes.Public, CallingConventions.Standard, new Type[] { source });
            var cbIlGen = cb.GetILGenerator();
            cbIlGen.Emit(OpCodes.Ldarg_0);
            cbIlGen.Emit(OpCodes.Ldarg_1);
            cbIlGen.Emit(OpCodes.Stfld, thatf);
            cbIlGen.Emit(OpCodes.Ret);
        }

        private static MethodBuilder MakeMethodWrapper(TypeBuilder tb, FieldBuilder thatf, string k, MethodInfo srcInfo, Type[] argTypes, Type retType, MethodInfo tgtInfo)
        {
            var methodType = argTypes[0];
            var mb = tb.DefineMethod(k, MethodAttributes.Public | MethodAttributes.Virtual, retType, argTypes);
            var mil = mb.GetILGenerator();
            mil.Emit(OpCodes.Ldarg_0);
            mil.Emit(OpCodes.Ldfld, thatf);
            mil.Emit(OpCodes.Ldarg_1);
            WrapValue(argTypes[0], srcInfo.GetParameters()[0].ParameterType, mil);
            mil.Emit(OpCodes.Callvirt, srcInfo);
            WrapValue(srcInfo.ReturnType, retType, mil);
            mil.Emit(OpCodes.Ret);
            string written = mil.ToString();
            if (tgtInfo != null)
            {
                tb.DefineMethodOverride(mb, tgtInfo);
            }
            return mb;
        }

        private static void MakePropertyWrapper(TypeBuilder tb, FieldBuilder thatf, string k, Type tgtType, PropertyInfo srcProp)
        {
            Type srcType = srcProp.PropertyType;
            PropertyBuilder pb = tb.DefineProperty(k, PropertyAttributes.None, tgtType, null);

            MethodAttributes gsAttr = MethodAttributes.Public | MethodAttributes.SpecialName | MethodAttributes.HideBySig;
            if (tgtType != null)
            {
                MethodBuilder getPropMthdBuilder = tb.DefineMethod("get_" + k, gsAttr, tgtType, Type.EmptyTypes);
                ILGenerator ilgen = getPropMthdBuilder.GetILGenerator();
                ilgen.Emit(OpCodes.Ldarg_0);
                ilgen.Emit(OpCodes.Ldfld, thatf);
                ilgen.Emit(OpCodes.Callvirt, srcProp.GetMethod);
                WrapValue(srcType, tgtType, ilgen);
                ilgen.Emit(OpCodes.Ret);
                pb.SetGetMethod(getPropMthdBuilder);
            }
            else if (srcProp.GetMethod != null) // src has getter, tgt doesn't, duplicate it through
            {
                MethodBuilder getPropMthdBuilder = tb.DefineMethod("get_" + k, gsAttr, srcProp.PropertyType, Type.EmptyTypes);
                ILGenerator ilgen = getPropMthdBuilder.GetILGenerator();
                ilgen.Emit(OpCodes.Ldarg_0);
                ilgen.Emit(OpCodes.Ldfld, thatf);
                ilgen.Emit(OpCodes.Callvirt, srcProp.GetMethod);
                ilgen.Emit(OpCodes.Ret);
                pb.SetGetMethod(getPropMthdBuilder);
            }

            if (tgtType != null)
            {
                MethodBuilder setPropMthdBuilder = tb.DefineMethod("set_" + k, gsAttr, null, new Type[] { tgtType });
                ILGenerator ilgen = setPropMthdBuilder.GetILGenerator();
                ilgen.Emit(OpCodes.Ldarg_0);
                ilgen.Emit(OpCodes.Ldfld, thatf);
                ilgen.Emit(OpCodes.Ldarg_1);
                WrapValue(tgtType, srcType, ilgen);
                ilgen.Emit(OpCodes.Callvirt, srcProp.SetMethod);
                ilgen.Emit(OpCodes.Ret);
                pb.SetSetMethod(setPropMthdBuilder);
            }
            else if (srcProp.SetMethod != null) // src has setter, tgt doesn't, duplicate it through
            {
                MethodBuilder setPropMthdBuilder = tb.DefineMethod("set_" + k, gsAttr, null, new Type[] { tgtType });
                ILGenerator ilgen = setPropMthdBuilder.GetILGenerator();
                ilgen.Emit(OpCodes.Ldarg_0);
                ilgen.Emit(OpCodes.Ldfld, thatf);
                ilgen.Emit(OpCodes.Ldarg_1);
                ilgen.Emit(OpCodes.Callvirt, srcProp.SetMethod);
                ilgen.Emit(OpCodes.Ret);
                pb.SetSetMethod(setPropMthdBuilder);
            }
        }

        private static void WrapValue(Type srcType, Type tgtType, ILGenerator ilgen)
        {
            if (srcType.IsEquivalentTo(typeof(object)) && tgtType.IsInterface) // * -> C
            {
                ilgen.Emit(OpCodes.Call, tyWrapperf.MakeGenericMethod(tgtType));
            }
            else if (srcType.IsInterface && tgtType.IsEquivalentTo(typeof(object))) // C -> *
            {
                ilgen.Emit(OpCodes.Call, dyWrapperf.MakeGenericMethod(srcType));
            }
            else if (srcType.IsEquivalentTo(tgtType)) { /* do zip */ }
            else
            {
                throw new CastException();
            }
        }
    }
    [System.AttributeUsage(AttributeTargets.Interface, Inherited = false, AllowMultiple = false)]
    sealed class SubtypeOf : Attribute
    {
        readonly Type[] of;
        
        public SubtypeOf(params Type[] of)
        {
            this.of = of;
        }

        public Type[] Subtypes
        {
            get { return of; }
        }
    }
}
