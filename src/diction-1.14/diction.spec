%define prefix     /usr

%define  RELEASE 1
%define  rel     %{?CUSTOM_RELEASE} %{!?CUSTOM_RELEASE:%RELEASE}

Summary: analyze text for style
Name: 		diction
Version:	1.13
Release: 	%rel
Copyright: 	GPL
Group: 		Text/Utilities
Source:		http://www.moria.de/~michael/diction/diction-%{version}.tar.gz
BuildRoot: 	/var/tmp/%{name}-%{version}-root
URL: 		http://www.moria.de/~michael/diction/
DocDir: 	%{prefix}/doc

%description
diction [desc]

%changelog
* Thu May 12 2000 HWN <hanwen@cs.uu.nl>
- Initial spec file copied GGV

%prep
%setup

%build

# Needed for snapshot releases.
if [ ! -f configure ]; then
  CFLAGS="$RPM_OPT_FLAGS" ./autogen.sh $ARCH_FLAGS --prefix=%{prefix} 
else
  CFLAGS="$RPM_OPT_FLAGS" ./configure $ARCH_FLAGS --prefix=%{prefix}
fi

if [ "$SMP" != "" ]; then
  (make "MAKE=make -k -j $SMP"; exit 0)
  make
else
  make
fi

%install
rm -rf $RPM_BUILD_ROOT

make prefix=$RPM_BUILD_ROOT%{prefix}  install

%clean
rm -rf $RPM_BUILD_ROOT

%files
%defattr(-, root, root)

%doc COPYING README 
%{prefix}/bin/*
%{prefix}/share/*
%{prefix}/man/*
