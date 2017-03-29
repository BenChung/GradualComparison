using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using System.Reflection.Emit;
using System.Runtime.Remoting;
using System.Text;
using System.Threading.Tasks;

namespace dyntest
{
    class CastException : Exception { }
    class Runtime
    {
        private static AssemblyName classGenName;
        private static AssemblyBuilder ab;
        private static ModuleBuilder mb;
        private static Type runtimeType;
        private static MethodInfo dyWrapperf, tyWrapperf;
        
        static Runtime()
        {
            classGenName = new AssemblyName("CastAssembly");
            ab = AppDomain.CurrentDomain.DefineDynamicAssembly(classGenName, AssemblyBuilderAccess.RunAndSave);
            mb = ab.DefineDynamicModule("KafkaWrappers", "KafkaWrapper.dll");
            runtimeType = typeof(Runtime);
            dyWrapperf = runtimeType.GetMethod("dyWrapper");
            tyWrapperf = runtimeType.GetMethod("tyWrapper");
        }

        public static dynamic dyWrapper<T>(T src)
        {
            return null;
        }

        public static T tyWrapper<T>(dynamic src)
        {
            Type source = src.GetType();
            Type target = typeof(T);
            PropertyInfo[] srcProps = source.GetProperties();
            PropertyInfo[] tgtProps = target.GetProperties();

            MethodInfo[] srcMeths = source.GetMethods(BindingFlags.Instance | BindingFlags.Public | BindingFlags.DeclaredOnly);
            MethodInfo[] tgtMeths = target.GetMethods();

            Dictionary<string, PropertyInfo> srcPropMap = srcProps.ToDictionary(val => val.Name, val => val);
            Dictionary<string, PropertyInfo> tgtPropMap = tgtProps.ToDictionary(val => val.Name, val => val);

            Dictionary<string, MethodInfo> srcMethMap = srcMeths.ToDictionary(val => val.Name, val => val);
            Dictionary<string, MethodInfo> tgtMethMap = tgtMeths.ToDictionary(val => val.Name, val => val);
            
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
            var cb = tb.DefineConstructor(MethodAttributes.Public, CallingConventions.Standard, new Type[] { source });
            var cbIlGen = cb.GetILGenerator();
            cbIlGen.Emit(OpCodes.Ldarg_0);
            cbIlGen.Emit(OpCodes.Ldarg_1);
            cbIlGen.Emit(OpCodes.Stfld, thatf);
            cbIlGen.Emit(OpCodes.Ret);

            foreach (string k in srcPropMap.Keys)
            {
                Type tgtType = null;
                MethodInfo tgtGet = null, tgtSet = null;
                if (tgtPropMap.ContainsKey(k))
                {
                    PropertyInfo tgtProp = tgtPropMap[k];
                    tgtType = tgtProp.PropertyType;
                    tgtGet = tgtProp.GetMethod;
                    tgtSet = tgtProp.SetMethod;
                }
                PropertyInfo srcProp = srcPropMap[k];
                PropertyBuilder pb = tb.DefineProperty(k, PropertyAttributes.None, tgtType, null);

                MethodAttributes gsAttr = MethodAttributes.Public | MethodAttributes.SpecialName | MethodAttributes.HideBySig;
                if (tgtGet != null)
                {
                    MethodBuilder getPropMthdBuilder = tb.DefineMethod("get_" + k, gsAttr, tgtType, Type.EmptyTypes);
                    ILGenerator ilgen = getPropMthdBuilder.GetILGenerator();
                    ilgen.Emit(OpCodes.Ldarg_0);
                    ilgen.Emit(OpCodes.Ldfld, thatf);
                    ilgen.Emit(OpCodes.Callvirt, srcProp.GetMethod);
                    ilgen.Emit(OpCodes.Call, tyWrapperf.MakeGenericMethod(tgtType));
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

                if (tgtSet != null)
                {
                    MethodBuilder setPropMthdBuilder = tb.DefineMethod("set_" + k, gsAttr, null, new Type[] { tgtType });
                    ILGenerator ilgen = setPropMthdBuilder.GetILGenerator();
                    ilgen.Emit(OpCodes.Ldarg_0);
                    ilgen.Emit(OpCodes.Ldfld, thatf);
                    ilgen.Emit(OpCodes.Ldarg_1);
                    ilgen.Emit(OpCodes.Call, dyWrapperf.MakeGenericMethod(tgtType));
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

            foreach (string k in srcMethMap.Keys)
            {
                MethodInfo srcInfo = srcMethMap[k];
                Type[] argTypes = null;
                Type retType = null;
                MethodInfo tgtMth = null;
                MethodInfo tgtInfo = null;
                if (tgtMethMap.ContainsKey(k))
                {
                    tgtInfo = tgtMethMap[k];
                    argTypes = tgtInfo.GetParameters().Select(param => param.ParameterType).ToArray();
                    retType = tgtInfo.ReturnType;
                } else
                {
                    argTypes = srcInfo.GetParameters().Select(param => param.ParameterType).ToArray();
                    retType = srcInfo.ReturnType;
                }
                var mb = tb.DefineMethod(k, MethodAttributes.Public | MethodAttributes.Virtual, retType, argTypes);
                var mil = mb.GetILGenerator();
                mil.Emit(OpCodes.Ldarg_0);
                mil.Emit(OpCodes.Ldarg_1);
                Type[] genericArgs = new Type[] { argTypes[0] };
                mil.Emit(OpCodes.Call, dyWrapperf.MakeGenericMethod(genericArgs));
                mil.Emit(OpCodes.Callvirt, srcInfo);
                mil.Emit(OpCodes.Call, tyWrapperf.MakeGenericMethod(new Type[] { retType }));
                mil.Emit(OpCodes.Ret);
                string written = mil.ToString();
                if (tgtInfo != null) {
                    tb.DefineMethodOverride(mb, tgtInfo);
                }
            }

            Type wrapper = tb.CreateType();
            ab.Save("KafkaWrapper.dll");
            return (T)wrapper.GetConstructor(new Type[] { source }).Invoke(new object[] { src });
        }
    }
    namespace Kafka
    {
        public interface IA
        {
            dynamic m(dynamic x);
        }
        public interface II
        {
            II m(II x);
        }
        interface IT
        {
            IT s(II x);
            dynamic t(dynamic x);
        }
        interface IC
        {
            IC n(IC x);
        }
        class A : IA
        {
            public A()
            {

            }

            public dynamic m(dynamic x)
            {
                return x;
            }
        }
        class I : II
        {
            public I()
            {

            }

            public II m(II x)
            {
                return x;
            }
        }
        class T : IT
        {
            public T()
            {

            }
            public IT s(II x)
            {
                return this;
            }

            public dynamic t(dynamic x)
            {
                return (dynamic)this.s((II)x);
            }

        }
        class C : IC
        {
            public C()
            {

            }
            public IC n(IC x)
            {
                return this;
            }

        }
        class Program
        {
            public static void Main(string[] args)
            {
                II rv = Runtime.tyWrapper<II>(new A());
                
                new T().t((dynamic)new A());
            }
        }
    }
}
